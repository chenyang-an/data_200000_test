variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43471684201025842593054427498 : ((((True ∧ ((p4 → ((((p1 ∧ (True ∧ p1)) → p3) ∧ (((p3 ∧ (p5 ∧ p4)) → (p1 ∨ p4)) ∧ p4)) ∧ p5)) ∧ p3)) ∨ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185701745889705720352958181566 : ((p2 → ((p1 → ((False ∧ False) ∧ (p4 → (True → p5)))) ∨ p4)) ∨ (((True ∨ (p3 → ((p2 → (p3 ∨ False)) ∧ p1))) ∧ p3) → (p2 ∨ True))) := by
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
theorem thm_5_vars_696335052845884407977400216278 : ((((p2 → (p1 → ((p4 → (p2 ∧ (False ∧ p3))) → (p2 ∧ (p3 ∨ True))))) → (p2 ∧ ((((p1 ∨ True) → (p4 ∨ p5)) ∨ False) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309632616805809602910061869849 : (p2 ∨ (((p4 → ((((p2 ∨ p3) → False) ∨ p5) ∧ False)) → ((p1 ∧ (p1 ∨ False)) ∨ (((True ∧ p1) ∨ p2) ∨ True))) ∨ ((False ∨ True) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_614017346800854996279090416949 : ((((((p1 ∧ (p2 ∧ p2)) → (((p1 ∨ p3) → ((p1 → (False ∨ p5)) ∨ (False ∨ (p2 ∧ p5)))) ∨ False)) ∨ ((p1 → p1) ∨ False)) ∨ p5) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606352067358892969781713673648 : (((((((((((True → ((True → p1) ∧ p3)) ∨ p1) ∧ (True ∨ True)) ∧ ((True ∨ False) → p4)) → p1) ∨ (False → p3)) ∨ p5) ∧ p2) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110852058424265971358447148944 : ((((((p2 ∧ (p5 ∨ (p4 ∨ (True ∨ (((p1 → False) ∧ p5) ∨ (p5 → (p1 ∨ (p1 ∧ p4)))))))) → p4) ∧ p1) → False) ∧ p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306653518700137672453302402974 : (p1 ∨ (True ∧ (((((((p1 → (p4 → p3)) → (False ∧ True)) ∧ (p4 → False)) ∨ False) ∨ p2) ∨ True) ∨ (p1 ∧ (p4 ∧ ((p3 → True) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_43052714081750138593028738173 : ((((((((False ∨ p1) → p4) ∧ (True ∧ (((p4 ∧ p1) → (p2 → ((p4 ∨ (p2 → p1)) ∨ p3))) ∨ p5))) ∨ p1) → False) ∧ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49171982092429464368570179904 : ((((True ∨ ((p5 ∧ (p2 ∨ p5)) ∨ p4)) → (p1 ∨ ((p1 ∨ ((p5 → True) → (p1 → p5))) ∨ (p5 → True)))) ∨ (p4 ∨ (p5 → True))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49437109817002755893648271732 : (((((p5 ∨ (((((p4 → p4) → (p3 ∨ p3)) ∨ p4) ∨ ((p2 → p1) → p5)) → p2)) ∨ (True ∧ False)) ∨ p2) → ((True → False) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712223996092865523474243909145 : ((((((p2 ∧ (True ∧ False)) → p4) → p4) ∨ (False ∧ (((((p4 → p5) → (True ∧ p4)) → True) ∧ ((p2 → (True ∧ p4)) ∨ p1)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66390075878044183466331625449 : ((p5 ∨ (p5 ∨ ((True ∧ (p2 → False)) → ((p2 ∨ ((p1 ∧ p2) ∧ ((p1 ∨ False) ∧ ((True ∨ (p5 → False)) → True)))) ∨ (p2 → p5))))) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717800528422671371367343689966 : ((((((p5 ∨ p4) → p2) ∧ False) ∨ (((p3 ∨ p4) ∨ (((p2 ∨ p4) ∧ (True ∧ (p5 ∧ (p3 ∧ ((p4 ∧ p5) ∧ p5))))) ∧ p1)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350962665364055998433719544211 : (p4 → (((((True ∨ (((p3 → False) ∧ p5) ∨ p1)) → p1) → p2) → ((True → p1) ∨ ((p2 ∧ p2) ∨ (p4 ∨ (p1 → p3))))) ∨ (p4 ∧ p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231056901180992499806366774079 : (((True ∨ p3) ∨ p1) → ((p4 → ((((False → True) ∨ True) → False) ∨ True)) ∨ ((p5 → p3) → (True ∨ (p1 ∧ (((False ∨ p5) → True) → p2)))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767671867916197607122159450526 : (((p5 ∧ ((p4 ∧ (((p5 ∧ ((p5 ∨ p1) ∧ p2)) ∨ (((p4 → p4) ∧ p4) ∧ True)) ∧ (p2 → (p3 → (p2 ∧ (p2 ∧ True)))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775657395647214108737570271088 : (((False ∨ (p1 ∨ ((True → (p4 ∨ p3)) ∨ ((False → ((((p5 ∨ p4) ∨ p2) ∧ p3) ∨ ((p4 → p2) → p3))) ∧ ((p5 ∧ True) ∨ True))))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248825498884450156183011195882 : ((p3 ∨ p4) ∨ ((p3 ∨ ((False ∧ p2) ∧ (((True → ((p4 ∧ p5) ∧ p3)) ∨ p3) → p5))) ∨ (((((p5 ∨ p5) ∨ p4) → True) ∨ False) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751963953351104619641946831870 : (((True ∧ (p4 ∨ (((p3 → (p2 → ((False ∧ True) ∨ p3))) → (False → (p2 → p1))) → (p5 ∧ ((p4 ∧ ((p4 → p4) → True)) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225214604637528906843907671705 : (((p5 ∧ False) ∧ p1) ∨ ((p3 ∨ p4) ∨ (((p5 ∧ True) ∨ p3) ∨ (True ∨ ((p5 ∨ False) ∧ (((p4 ∨ (p5 ∧ p1)) ∧ (p1 → p2)) ∨ False)))))) := by
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
theorem thm_5_vars_808018233266972523684314013735 : (((p4 → (True ∧ ((True ∧ ((True → (p4 ∨ (p3 ∨ (p4 ∨ p1)))) → (((p3 ∨ p4) ∧ (p2 ∨ (p1 ∧ (True → p2)))) ∨ p5))) ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201956909838388914059985177125 : (((p4 ∨ (p1 ∨ (True ∨ p5))) ∨ p4) ∧ (((((p5 → p4) → p5) ∨ (p5 ∧ p3)) → p4) ∨ (((p5 ∧ p3) → (p5 → (p2 → True))) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43923764505303031700945234907 : ((((((((((p1 ∨ p2) → True) ∧ (p1 → p1)) → (p4 ∧ p1)) ∨ p1) ∧ (p4 → (True ∨ False))) ∧ (p3 → p5)) ∨ (True ∧ p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184087247117314243561435548755 : ((((p5 ∨ (False ∨ False)) ∧ (((p3 ∧ p1) ∧ p4) ∧ p2)) ∨ p5) ∨ ((p3 ∧ (False ∧ (((p4 → p3) → (p5 → p1)) ∧ False))) → (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356180025470147470362645320151 : (p5 → ((((p1 ∧ (((((p4 → (False ∨ True)) → True) → False) → p4) ∧ (True → p4))) → p3) ∨ p2) → (p1 ∨ (((p1 ∧ p4) ∧ p3) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61179560922370389959430153141 : ((False ∧ ((True ∧ p5) ∧ (p1 ∧ ((p4 ∨ (p1 ∧ (False → (True ∧ (False ∨ ((((p1 ∧ p5) ∨ p2) → False) ∨ p3)))))) ∨ (p2 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68736606416751002279469141677 : ((p4 → (((p1 → ((p4 → p3) ∨ (((p2 → (p1 → (p2 → False))) ∧ p4) ∨ (p4 → p4)))) ∨ p2) → ((p1 ∧ p3) ∨ (p5 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355067995974880984920270183707 : (p5 → ((((p2 ∧ (((p2 ∧ ((False ∧ p3) ∨ True)) → p1) ∧ (((p3 → p4) → p4) ∧ ((p1 ∧ p4) → (p3 → p2))))) ∨ p5) → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ (((p2 ∧ ((False ∧ p3) ∨ True)) → p1) ∧ (((p3 → p4) → p4) ∧ ((p1 ∧ p4) → (p3 → p2))))) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299450939640137216133162920806 : (False ∨ ((p3 ∨ ((p5 ∧ ((True ∨ False) → ((((False → False) ∨ (p1 ∧ False)) → p4) ∧ (p3 ∧ ((p3 ∨ (p1 → True)) ∨ False))))) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52634672867920567778698721064 : ((((p2 ∧ p5) ∨ ((p2 → ((True → p2) ∨ True)) → (p2 ∧ (True ∧ True)))) ∨ ((p3 → (p1 ∨ ((p2 ∧ p4) → p4))) ∨ (False ∧ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258794179863595336823665379723 : ((True → False) → (((p1 ∨ p5) ∨ p5) ∨ (True → ((p4 ∨ ((p1 ∧ (p1 ∧ p2)) ∧ ((p5 ∨ (False ∧ p5)) ∧ (p3 → False)))) ∧ (p2 ∨ p5))))) := by
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
theorem thm_5_vars_691191533018638407437923590321 : ((((((p2 → (p4 ∨ p1)) ∧ (p2 ∧ p1)) ∨ (p3 ∧ ((p3 → (p1 ∧ p5)) → p2))) → ((p4 ∧ p4) ∧ (p3 ∨ ((p3 → p3) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610103712911463111970373324594 : ((((((True ∧ (p3 ∧ (p5 → (p4 ∧ (((False → p3) → (p2 ∨ (((p2 ∨ (True ∧ p1)) ∧ p2) ∧ p5))) ∧ True))))) ∧ p4) → p5) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130633016152323606394523105788 : ((((((p5 → p4) → p5) ∧ (((p1 → p3) → True) ∨ p5)) → ((p1 ∧ p4) ∨ p2)) ∨ (False → ((p5 ∧ p4) ∧ p2))) ∧ ((False ∧ True) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349946299253427881667150391531 : (p4 → ((((((p1 → p2) ∨ p4) → (((p2 → p1) → (((p4 ∨ p3) → ((p1 ∨ p3) ∨ p1)) ∧ p1)) ∨ p4)) ∧ (p3 ∧ p2)) ∧ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217624612246859207329171775997 : ((((False ∧ p1) → p4) → p5) → (p4 ∨ (False ∨ ((((((p3 ∧ (False ∧ False)) → p4) → (p2 ∧ True)) → (p4 → p1)) ∧ (p3 ∨ True)) → p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : ((False ∧ p1) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : ((False ∧ p1) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h12
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231950891006918610746962527680 : (((p1 ∨ p1) → p1) → ((((((p3 → p5) ∧ p4) → p5) ∧ p3) ∧ (((p5 ∨ p2) ∨ True) ∨ (p3 ∧ p2))) ∨ ((p2 → (p3 ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156821137218469502954855843663 : (((p4 ∨ (((p4 ∧ (False ∨ (False ∨ ((p5 → (False ∧ p1)) ∨ True)))) → (p2 ∨ False)) ∨ True)) ∧ p2) ∨ ((p2 → (True ∨ (p2 → p4))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67918176505946868001702426877 : ((p2 → (((p2 ∧ p5) ∧ ((p3 ∨ (p3 → p1)) ∧ ((p3 ∨ True) ∨ p1))) → ((((p2 ∧ (p2 ∨ False)) → (False ∨ p3)) ∧ True) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666733944928683923555842645662 : ((((((p1 ∧ ((p2 → ((True ∨ p3) ∨ p3)) ∨ p5)) → p3) → (((p2 ∧ p3) → ((p2 ∧ p5) ∨ p5)) ∨ False)) ∧ ((True → True) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217486065267357520658440320447 : ((((p4 ∧ p3) ∧ p5) → True) → (((p5 ∨ (p3 → (False ∨ False))) → (True → False)) ∨ ((p1 → p5) → (p5 → (False → (p3 → (p3 ∧ p3))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662694515033050576300632216333 : ((((((p2 ∧ p5) ∧ (p5 ∧ p2)) ∨ (((((False ∨ p3) → (True ∧ (True ∧ (True ∧ False)))) ∧ p5) ∨ (p5 ∨ p4)) → p2)) → (p2 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266264773796266412171410836288 : (True ∧ (p5 → (((p4 ∧ ((p1 ∧ ((p3 ∧ False) ∨ False)) ∨ p2)) ∧ p1) ∨ (True ∨ ((p5 ∨ ((p2 ∧ p3) ∧ ((p5 → p1) → p1))) ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264033275715562780582996302861 : (True ∧ (((p3 → ((p4 → p4) ∨ ((True ∧ p5) ∨ True))) ∨ p2) ∧ (((False → (p3 ∧ False)) → p5) ∨ ((False ∧ (p1 ∧ p1)) ∨ (False ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458252085607952145741561402919 : (((((p3 ∨ p5) ∨ ((p5 ∨ (p2 ∨ ((p3 ∧ (p4 ∧ p2)) → False))) ∨ (p5 ∨ (p4 ∨ p5)))) ∨ ((p5 → True) ∨ ((p1 ∧ p4) ∧ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937806000110448132197833079557 : ((((p5 ∧ (p5 → ((True → False) ∨ p2))) ∧ (((p3 ∧ p3) ∧ (p2 ∧ p2)) → (p4 → ((True ∨ ((p1 → (p3 ∧ False)) ∨ p1)) ∧ p1)))) → p2) ∧ True) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8968855070100137569121082367 : ((((((p1 ∨ (p4 ∧ (((p4 ∨ (p1 → False)) → p1) → p5))) → (p2 ∧ True)) ∧ p2) ∨ (p1 → (False ∨ (p3 ∨ (p1 → True))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49019115595382229294977890204 : (((((p3 → (p2 ∧ ((((p2 → (False → p4)) → p2) → (True ∨ p2)) → (p5 ∧ p4)))) → (p4 → p1)) → p5) ∨ (False ∨ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_975580257339238121310223100470 : ((((p5 → True) → ((False ∨ (p5 ∧ (p1 ∧ ((p2 ∨ (((p3 ∨ (p3 ∧ True)) ∨ ((p1 ∨ True) ∧ p1)) ∧ p1)) ∨ (p1 ∧ p1))))) ∧ False)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341087899312560824232851186248 : (p2 → ((p1 → (((p4 ∧ (p4 ∧ (False ∧ False))) ∧ (p4 ∧ ((p1 → (p2 → p5)) ∧ (False ∧ False)))) ∨ ((False ∧ (p1 → False)) → p3))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53834447716570565470105273783 : ((((((p5 ∧ p1) ∨ p4) → False) ∧ (False → (p4 ∧ p5))) ∨ (((((p5 ∧ p4) ∨ (p2 ∨ p5)) ∧ p5) → p3) ∧ (p4 ∧ (False ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134620515972126427601666648766 : ((((((p2 ∨ (p5 ∨ ((((p2 → p1) → p5) ∧ p3) ∧ p1))) ∧ p5) ∧ (False ∨ p4)) → ((p4 ∨ p4) ∨ p1)) → p2) ∨ (True ∨ (False ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241528366913243729040858438305 : ((False → p3) ∧ (((((p1 → (p5 → (p3 ∨ p1))) → (p3 ∨ p4)) ∧ (((False ∨ False) → p4) ∧ (p4 ∨ p2))) → (p4 ∧ p3)) ∨ (True ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40313034178696479208393128774 : ((((((p4 ∧ (p5 ∨ p3)) ∨ ((p4 ∧ (p3 ∧ (True → (p4 → p2)))) → (p1 → (((p4 → False) ∧ p4) ∨ p3)))) ∧ p3) ∨ p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38116606123668975993579010340 : ((((((((True → (p1 ∧ p3)) → p5) ∨ ((True ∧ ((p4 ∨ False) → True)) ∨ p2)) ∨ p4) ∧ (p5 → p2)) ∧ (p2 → (p1 → p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134052638906145307945113686003 : ((((False ∨ (((p1 ∨ (p4 ∨ True)) ∨ (p2 ∨ (p4 ∧ p3))) ∧ (p2 → (((p4 ∨ p3) ∨ p4) → p1)))) ∨ False) ∨ False) ∨ (False → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137142679108346464753923843134 : ((True ∧ (p1 → ((((True ∨ (p2 ∨ p2)) → False) ∧ (p4 → (((p1 → (p5 ∨ (False → p2))) ∧ p1) ∧ p3))) ∨ p3))) ∨ (True ∧ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314504258432188958850030922166 : (p3 ∨ ((((((p1 ∨ p4) ∧ p2) ∨ ((True → (p3 ∨ False)) → (False → p4))) ∨ p3) ∧ (p3 ∨ True)) ∧ (False ∨ ((True → (False ∧ p5)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_310802620700415733868280269812 : (p2 ∨ ((p2 ∧ (p5 → False)) ∨ (p4 → (((((p5 ∨ p1) ∧ (p1 ∧ ((False → (((p1 ∧ True) ∧ p2) → False)) ∧ False))) ∨ True) ∧ True) ∧ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44950215842993941925341523970 : ((((p1 ∨ p2) ∧ (False ∨ (True ∧ (((p3 ∨ p5) ∨ p1) → (((p4 ∧ p1) ∨ (p5 ∧ (True → p1))) ∧ (p2 ∧ (p2 ∨ True))))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114968833925798410114142639907 : (((p4 → ((p2 → ((p3 ∧ p2) ∧ ((p1 → False) → (p1 ∨ p1)))) → p4)) → ((((True → p4) ∧ p5) → p3) ∨ (p4 ∨ p1))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118700534091030265616360195371 : ((p5 ∨ (((((p2 ∧ p2) ∨ (((p4 ∧ ((p5 → (True ∨ (False → p2))) → (p5 ∨ True))) → True) ∨ p3)) ∧ p5) ∧ p4) → p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901878144918074678465090557270 : ((((((p1 ∧ ((((((p2 → p5) → (p4 ∨ p5)) → True) → p5) ∧ True) → (p2 ∨ False))) → True) → False) ∧ ((p4 ∨ p2) → (p5 ∧ p4))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∧ ((((((p2 → p5) → (p4 ∨ p5)) → True) → p5) ∧ True) → (p2 ∨ False))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310636713236539005618847723053 : (p2 ∨ ((p4 ∧ (p1 ∧ (True ∧ p2))) ∨ (p1 → ((False → (True ∧ True)) ∧ ((p4 ∧ (False → True)) ∨ ((p5 ∨ False) ∨ (p4 → (True ∨ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38802748105684974916097144699 : ((((((p3 ∨ p5) ∨ True) ∧ p1) → (p5 → (((((p1 ∨ False) ∨ ((p5 ∧ p3) ∧ True)) → p4) ∧ p1) → ((p2 ∧ p2) ∧ p3)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62175186340873256233689163008 : ((p2 ∧ (p5 → ((False ∧ (p1 ∨ (((p4 ∧ (p2 ∨ (((p5 ∨ (p5 ∧ p2)) ∨ p1) ∨ (p5 ∧ False)))) ∨ p2) → (p1 ∧ p5)))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263156581211216762176956061318 : (True ∧ ((p3 ∧ ((((p4 ∧ p1) → ((p2 ∧ (p2 ∧ True)) ∧ p1)) → (p5 ∨ ((p1 ∧ p2) → (True → (p1 → p4))))) ∨ True)) ∨ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598710999058138814844637280129 : (((((True ∧ True) ∧ (((p4 ∨ p3) ∨ (False ∨ p1)) ∨ ((False ∨ (p5 ∨ (p3 → p3))) → (True → (p3 ∧ (True ∧ (p4 ∧ p5))))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665157784110219791093376223018 : ((((((p5 ∧ (p1 → (((False ∧ (p5 → (False ∧ True))) ∧ p3) ∨ (p2 → (p1 ∧ (False ∨ p3)))))) ∧ p4) ∧ p4) ∧ (p1 ∨ (False ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707258668550900544057651216055 : ((((((p4 ∨ p2) ∧ (p1 ∧ p3)) ∧ (p4 ∨ p3)) ∨ (((False → (p1 ∨ ((True → p3) ∧ (p1 ∨ p2)))) ∨ False) ∨ ((p2 → True) ∨ False))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317034281969645400602268409660 : (p3 ∨ (p4 → (((((((p4 → (p5 ∨ ((True ∨ p1) → p2))) → p2) → (p4 ∨ (p5 ∧ True))) → p1) → (True ∧ p1)) → (True ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59675522571830083031786162224 : (((True ∧ p2) → (p1 → (((True ∨ ((p3 ∨ (p3 → True)) ∨ (p2 ∨ (p3 ∨ (p2 ∧ (p5 ∨ ((p4 ∧ p1) ∧ True))))))) ∧ p2) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186629972728223388475835773962 : (((p4 ∧ (p3 ∧ ((p4 → (p5 → p4)) → p5))) → (p4 → p1)) → (p1 ∨ ((p2 ∧ ((p2 → p1) ∨ (p5 ∨ (p3 ∨ (p1 ∨ p1))))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788799105461209557329128088974 : (((p5 ∨ ((p3 ∨ ((p4 → ((p1 → ((p3 → (p1 ∨ (False → (p4 ∧ p2)))) → p1)) → (False ∨ ((p5 → p4) ∧ p1)))) → p2)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706170567907967873968862146801 : (((((p5 → p5) → (False → ((p1 → True) → p5))) ∧ (p3 ∧ ((p3 ∨ p3) ∨ (((p4 → p5) ∧ ((True ∧ p5) ∧ (p5 → p1))) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788361336671000763638236008124 : (((p5 ∨ (((((False ∨ p3) ∧ ((p2 ∧ False) ∨ (p3 → (p5 ∨ ((((p4 ∧ False) ∧ p4) ∧ p3) → False))))) ∧ p5) ∧ (True ∧ p2)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_136874408539899086425685108841 : (((False ∨ p4) ∨ (p5 → (p3 → (((p5 → ((p5 ∧ p1) ∨ True)) → (p1 ∧ False)) ∨ (p3 ∧ (False → (p5 ∨ p3))))))) ∨ ((p4 ∨ p4) → p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216125557518720596965852842964 : ((True → (p2 ∨ (p2 ∧ p5))) ∨ (((p3 ∨ ((True ∧ (True → (p2 ∧ (p2 ∧ p4)))) ∨ (((p5 → p5) ∨ p4) ∨ p2))) ∧ True) ∨ (p5 ∧ True))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595587890293421406888724723618 : (((((((p1 → (((p2 ∧ (p4 ∨ p4)) → True) ∨ p2)) → p2) → p3) → ((((True ∧ p5) → p1) ∧ (True ∧ (True ∨ p4))) ∨ True)) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_200231015581387319705696947519 : ((((True ∨ True) ∨ False) → ((False ∨ p4) ∧ p3)) → (p2 ∨ ((False ∨ (p4 ∨ p4)) ∨ (p4 → ((p5 ∧ (p3 ∨ p4)) → (p4 → (p1 ∧ False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337374891438266340041353675400 : (p1 → (((p5 ∧ ((p3 → False) → p1)) → ((p5 ∨ p1) → (True → (p3 ∧ ((p1 ∨ (False → (p3 ∧ p2))) ∧ p3))))) ∨ ((True ∨ p2) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654862661487271113647409295202 : ((((((p5 ∨ ((p4 ∧ p3) ∧ (((p5 ∨ (p5 ∧ ((p1 ∨ p4) ∧ p5))) ∧ p1) ∧ p5))) → (p1 ∨ (True ∨ p3))) → p4) ∨ (p1 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_791673557375672714025656442538 : (((True → (((p3 ∨ ((True ∨ ((p3 ∨ (p3 ∨ p4)) ∨ True)) ∨ p2)) ∨ ((p1 → (True ∨ (p1 ∧ True))) → (p3 ∧ (p4 ∨ p1)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204125255361052679239618093693 : ((((False ∧ (p2 → False)) ∧ p5) ∧ p2) ∨ (((((p1 ∨ p5) ∧ True) ∨ ((p5 ∨ p2) ∨ False)) ∧ (p1 ∧ (p3 ∨ (p5 ∧ p2)))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114874140899316603594139219852 : ((((True ∧ (True ∧ p2)) ∧ ((False ∨ (p5 ∧ p4)) ∨ (p3 ∨ (True → False)))) ∨ (True ∨ (((p2 → False) ∨ p1) → (p1 → p2)))) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207912785329850002211708706087 : (((p4 ∧ (p4 ∨ p5)) ∧ (p1 → p5)) → ((True ∧ (False → p3)) → ((p3 ∨ ((True ∧ (p4 → False)) → True)) ∧ ((p4 ∨ p5) ∧ (p4 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h21 := h2.left
  let h22 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- One of the premise coincides with the conclusion.
    exact h27
  case inr h28 =>
    -- One of the premise coincides with the conclusion.
    exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354581655557551886330819539538 : (p5 → ((((p1 → (False ∨ p2)) ∧ (((True → p3) ∨ (p5 ∧ ((p3 ∨ ((p2 → p5) ∨ False)) → (p2 ∨ (p3 → p4))))) ∧ False)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610671913433654713657035146890 : (((((((((p5 ∨ False) ∨ ((p5 ∨ True) → (((p3 → True) ∨ p1) ∨ p4))) ∨ (p3 ∧ True)) → True) ∧ (p4 → (p3 → p1))) → p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_20231902594192977588821263273 : ((((True ∨ (p1 ∧ ((p4 ∨ p3) ∨ (p2 ∨ p4)))) → (False ∨ (p1 ∨ True))) ∨ (False ∧ (p3 → (((p1 ∧ False) → (p5 → True)) ∧ False)))) ∧ True) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50620594144272873425929635257 : ((((False ∨ ((True ∨ ((p4 ∨ (p4 ∧ (True → True))) ∧ True)) ∨ (True ∧ p2))) ∧ ((p3 → p3) ∨ p1)) → ((p4 → p3) → (p2 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45637905642713751635967520871 : (((p4 ∨ ((((p5 → (p4 → (((p1 → True) ∨ p3) ∧ p3))) → p3) → p1) → (((p3 → (p3 ∨ p1)) → False) ∧ (p3 ∨ p4)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648424315224991868953930290758 : ((((((((p5 → (p2 → ((p3 ∨ (p5 → False)) ∨ ((p1 ∧ False) ∧ p4)))) ∧ (p5 ∧ (False → p1))) ∨ False) → p2) ∨ True) ∧ (p3 ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21093736362019832772625850500 : ((((p5 ∨ p4) ∧ (((p4 ∧ True) ∨ ((p5 → True) ∨ False)) ∨ True)) → ((True → ((p2 ∨ ((True ∧ p1) ∨ p3)) → (True ∧ p2))) ∨ True)) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110707299863404372059195281129 : (((((((True ∨ True) ∧ (False ∨ p3)) → ((p4 ∧ ((((False ∧ p1) ∧ True) ∨ (p1 → p1)) → p2)) → p1)) ∨ p5) ∧ p2) ∧ True) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54703060483885918213313562316 : ((((((p4 ∧ p4) ∧ p4) ∧ p4) ∨ (p4 ∨ p1)) → ((((p5 → p4) ∧ (False ∧ (p4 → ((p2 → p2) ∨ p4)))) ∨ p4) ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164968915321225090504289963729 : ((((((p3 ∧ True) ∨ (((p1 ∧ True) → p1) ∨ (p1 ∧ p4))) ∧ p5) ∨ (p2 → False)) → p4) ∨ (((p2 → (p2 ∨ p1)) ∧ p1) → (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68729190685519330520815985159 : ((p4 → (((p5 ∧ (p2 ∨ ((p1 ∧ p4) → p1))) ∨ (True ∨ (((p5 → p5) ∨ p2) ∧ (p2 ∨ False)))) ∧ ((p2 ∧ p3) ∨ (p1 ∨ p4)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303028592777597720969129361370 : (False ∨ (p1 → (p3 ∨ (((True ∧ p5) ∧ False) ∨ (p1 ∧ (True → ((p3 ∨ (p1 ∨ ((p2 ∧ p2) → ((p5 ∨ True) → (False ∧ p1))))) ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1770423175071278375784765035 : ((((((p4 ∨ ((p2 → (False ∨ p5)) ∧ (p1 → (False ∧ (False ∧ (p5 ∨ p1)))))) ∧ p2) → p3) ∨ False) → p4) ∨ (True ∨ (p3 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



