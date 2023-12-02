variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204238090385457655840774427075 : ((((p4 ∧ p2) ∧ (p2 ∨ p4)) ∧ p1) ∨ ((False → (p1 ∨ ((True ∨ p5) → ((p5 → (p3 → (p3 ∧ p4))) → p3)))) ∨ ((p3 → p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181051607089433823355320752216 : (((p1 ∧ p5) → ((p2 ∧ p1) ∨ (((p5 → p4) ∨ (False ∧ True)) ∨ p5))) → ((p4 ∧ (p4 ∨ ((p2 → False) ∧ (False → False)))) → (p4 ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750977745844710161606559827530 : (((True ∧ (((p4 → (True → p5)) ∨ (p3 ∨ p3)) ∨ ((p2 → p3) → (((False ∧ (False → p2)) ∧ (p5 → ((False ∨ p1) → p5))) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69278017493824513449017010789 : ((p5 → ((p5 → p4) ∨ ((((((p4 → (p2 → (True ∧ False))) ∨ ((False ∨ p2) → p2)) ∧ p2) → p5) ∨ (False ∨ False)) ∧ (p4 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55240537396706418732662074031 : ((((p3 ∧ p1) ∧ (p2 → (p5 ∨ True))) ∨ (p1 ∧ ((((True → False) → (p4 ∧ p1)) → p5) ∨ (p1 → (((p3 → p3) ∧ p3) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41215189701308212755764683231 : ((((((p5 ∨ (p2 ∧ (p5 ∨ p3))) ∨ ((((True ∨ p3) ∨ True) ∨ False) ∨ (p2 ∧ p2))) ∨ p2) ∧ (((p2 ∨ p4) ∨ p3) ∨ p1)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691960672597592130525764305229 : ((((p4 → (p1 ∧ ((False ∨ (True ∧ (((p5 → p1) ∨ p2) → p5))) ∧ (p5 → p1)))) → ((p1 → (p2 ∧ ((p1 ∧ p1) → p2))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656004301824136428974968409784 : ((((((p5 ∧ p4) ∧ (True ∧ (((((p1 → p2) → p3) ∨ (p4 → p1)) ∧ p2) → p3))) ∨ (p5 → ((False ∧ True) ∨ p2))) ∨ (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180182746250784725035594742755 : (((((True → (p2 ∨ p4)) ∧ p1) ∨ ((True ∨ (p4 ∧ p1)) ∨ True)) → False) → (p5 ∨ (True ∧ ((p3 ∨ ((p4 ∧ (p1 ∨ p2)) → p3)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → (p2 ∨ p4)) ∧ p1) ∨ ((True ∨ (p4 ∧ p1)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715163570683312008704407427844 : ((((True → (((p5 → p1) ∨ p5) ∨ p1)) → (((False ∧ ((p3 ∧ p3) → (p3 → (p2 → ((p3 ∨ (p4 ∧ True)) → p4))))) ∨ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204843839663593717143710568100 : (((((p1 ∧ p4) ∧ p4) → False) → p4) ∨ (p5 → ((((p4 ∨ (p2 ∨ (p1 ∧ ((True ∧ p5) → (p4 → p4))))) ∨ p5) ∧ (p1 ∨ p5)) ∧ True))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172617123167539429091219608563 : (((True ∧ p2) ∧ (p5 ∨ (True ∧ ((((p1 ∨ p3) ∨ False) ∧ (p3 → False)) ∨ p5)))) ∨ (False → ((((True → False) ∨ True) → False) ∧ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801127386369156313848322984630 : (((p2 → ((p4 ∨ (((False ∧ ((((p1 → p3) → (False → p1)) → (p5 → p4)) ∨ True)) ∨ p2) ∧ p4)) ∧ (True ∨ (p2 → (p5 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137861486547472625082140825239 : ((p3 ∨ (p5 ∧ ((p4 ∨ (False → (((False → (True ∨ False)) → p2) → p4))) → (p5 ∧ ((p4 ∧ (False ∨ p4)) → False))))) ∨ ((False ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172427084743437794836952753556 : (((p2 ∧ ((p2 ∧ p4) → p1)) ∧ (p4 ∨ (False ∧ ((p3 ∨ p3) → (p1 → p2))))) ∨ (((p5 ∧ ((p3 ∨ p4) ∧ (p5 ∨ p3))) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341988245059714629401097274076 : (p2 → ((((p1 ∨ p3) ∧ ((p3 → (p4 → ((False ∧ (False → p4)) ∧ p4))) ∧ p5)) → (p4 → ((p4 → p5) ∧ p3))) ∨ (p5 ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_231266824421015047394122066268 : (((p4 ∨ p5) ∨ p3) → (p1 ∨ (p3 → (((True ∧ (p4 → False)) ∧ (False → (((p2 → p3) → (p1 ∧ (True ∧ True))) ∧ p1))) → (p5 ∨ True))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114441447059417369024476113101 : (((True → (p4 ∨ (p1 ∨ ((False → ((False → p5) ∨ (p5 ∨ True))) ∧ (p2 ∧ (True ∧ p3)))))) ∨ ((p3 ∨ True) ∨ (p2 → p5))) ∨ (p5 → p1)) := by
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
theorem thm_5_vars_320987571474378530581705838538 : (p4 ∨ (False ∨ (((((p1 → (((((True ∨ (p5 → p5)) → p4) ∨ (True ∧ False)) ∧ p5) ∨ p4)) ∧ False) ∧ (p4 → (False ∨ p3))) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184755530826317000185055466907 : ((((p2 → p4) → (False ∧ p3)) ∧ ((p2 → p3) ∨ (p2 ∨ False))) ∨ ((False ∧ p1) ∨ (((True ∧ (p5 ∨ True)) ∨ (False ∧ (p4 → p1))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157599604163346611707798990544 : (((p2 → ((((p5 ∨ (p1 ∧ (p5 → p4))) ∧ p5) ∨ ((True ∧ p1) ∨ p4)) → p2)) → (p4 ∧ p2)) ∨ ((True → False) → (p3 → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657952815172856964069552414934 : ((((p1 ∧ (True → (((p4 ∧ False) ∨ p4) ∧ (((p2 ∨ (p3 → (False ∧ (p4 ∨ (p2 ∧ p4))))) → (p5 ∨ p3)) ∧ True)))) ∨ (p5 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68615624123410805996969542799 : ((p4 → (((((p1 ∧ (p5 → (p2 ∨ (True ∨ p4)))) ∨ p2) ∧ False) ∧ (True → ((p4 ∨ (True ∨ (p2 ∨ p1))) → (p2 ∧ p4)))) ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136334998631894380822427535822 : (((True ∧ (p5 ∧ (p4 ∨ p3))) ∧ (False ∨ ((p4 ∧ ((p1 ∨ ((p3 → (p3 ∧ p5)) ∧ p3)) → p4)) ∧ (True ∨ False)))) ∨ ((False ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133788632843805717246633146689 : ((((p3 ∨ (p5 ∨ p3)) ∧ ((p5 ∨ ((False ∧ ((True ∧ (p5 → (p3 ∨ p2))) ∨ p1)) ∧ (True ∧ False))) ∧ p4)) ∧ p1) ∨ ((p5 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51877102695438453053472277211 : ((((p5 ∨ ((p3 → (p5 ∨ p1)) ∧ ((p3 ∨ True) ∧ (p5 ∧ (p5 ∨ p4))))) ∨ p1) ∨ (False ∨ ((p4 ∨ True) ∨ ((p3 ∧ p1) ∧ p1)))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344592717338781826404066332493 : (p2 → (p1 → ((p1 ∧ (p3 ∨ (((p3 ∨ p4) ∨ (p5 → ((p5 ∧ (p1 ∨ (p5 ∨ ((p3 ∨ True) ∨ (p1 ∧ p3))))) → p3))) ∨ False))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184038405836132979881792790179 : ((((p2 ∧ (((p4 ∨ (p5 → p5)) ∨ p3) ∨ False)) → p4) ∨ p3) ∨ ((p5 ∨ (p3 → p2)) → (False ∨ ((p4 ∧ False) → ((p5 ∧ p1) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h10.left
    let h15 := h10.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323470298862244735485316268047 : (p5 ∨ ((((((p1 ∨ (p1 → p3)) ∨ p1) ∨ p3) → (p2 ∧ ((p5 ∧ ((False ∨ p4) → p3)) ∧ (False → p5)))) ∧ p2) ∨ (True ∨ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329371797098546998875760142640 : (True → ((p2 ∨ (p3 → True)) → (p3 ∨ (((((False → (False ∧ p3)) ∧ p4) ∨ (p5 ∨ p5)) ∧ p5) → ((p3 ∨ p5) ∧ ((p2 → True) ∨ p2)))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
    -- Conjunctions on the left can always be decomposed.
    let h31 := h22.left
    let h32 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h36
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h39
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h40 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h41
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207552250164174638043042860278 : (((((p1 → p4) ∧ p2) ∨ p4) → p1) → ((((False → (((((p3 → (False ∧ p2)) ∨ True) ∨ True) → p5) ∨ True)) → False) ∨ (p3 → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147517042756261730379026037334 : (((p4 ∨ (((p1 → (p5 ∧ (True → (False ∧ p3)))) → p1) ∨ (p4 → ((False → (True ∧ p1)) ∨ True)))) ∨ p3) ∨ (((False ∧ p1) → p2) → p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667759306099480931516984588064 : ((((p5 ∧ (p4 ∨ (p3 ∨ ((p1 ∧ (p1 ∧ (p5 → (p5 ∧ p4)))) ∧ ((((False ∧ p4) ∧ p1) → False) ∨ p3))))) ∧ ((p1 → p2) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14711105155832195120165974994 : ((((p4 ∨ (True → (((((p4 ∨ (False ∨ p5)) → p2) ∧ (p1 ∨ ((p2 ∧ p5) → p1))) ∨ False) ∧ p4))) ∨ (p2 ∨ p4)) ∨ (p5 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_255666783338381264321416759125 : ((p5 ∧ p5) → ((((((p4 ∧ ((p5 → False) → p1)) ∨ ((((p3 → p3) ∧ p1) ∨ p5) → p4)) → False) ∨ (p3 → True)) ∨ (p4 ∧ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612449940646666026312860869837 : (((((((p2 ∧ ((((p3 ∨ (p1 → p4)) ∧ (p2 ∧ (True ∨ (False ∨ (True ∧ False))))) → p3) ∧ p5)) ∨ p2) ∧ p3) ∨ (p2 → True)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302853581874249517520112024904 : (False ∨ (p5 ∨ (p5 → ((((True ∨ p3) → (p5 ∧ p3)) ∨ p1) ∨ (((p4 ∧ (p2 ∧ p4)) ∧ p4) ∨ (p1 ∨ ((p2 → (False → False)) ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221618597312445442674600412692 : (((p4 → p4) ∨ p5) ∧ (((False ∨ False) ∧ (((((p3 → (p3 ∧ ((True ∧ (p4 ∧ p2)) ∧ p2))) → p3) → p3) → p5) ∧ (p1 ∨ p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319282155315682761321354383188 : (p4 ∨ (((p4 ∧ p1) ∨ ((p1 → ((p1 → p3) ∧ ((p4 ∨ p3) ∨ p1))) ∨ (p5 ∨ True))) ∨ (False ∨ ((p1 → (p1 ∧ (True ∨ p2))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_756380561787183350238453018724 : (((p1 ∧ (((p3 → (((p5 ∨ p2) ∧ (((((p3 → p1) → p3) ∧ p1) ∧ p2) → (p5 ∨ p5))) → False)) ∧ True) ∨ (p2 ∧ (False ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199734006229493503914909079926 : (((p1 ∨ (p1 ∧ ((p2 ∧ p4) ∧ p3))) → p3) → (True → (((((p4 ∧ ((p2 ∨ False) ∨ p1)) ∨ False) ∧ (True → p2)) ∧ (p4 ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134764048030625949155096180689 : ((((True → p3) → (((((p1 ∧ (p1 ∨ ((p4 ∨ (p1 ∧ False)) → p4))) → p2) ∧ True) → p5) → (p5 → p3))) → p1) ∨ ((False → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61796621831686606924653569010 : ((p2 ∧ ((((((p1 ∨ p5) ∨ p5) ∧ (p5 → p4)) ∧ ((((p2 ∨ False) → (((p5 ∨ p3) ∧ p5) ∧ p5)) ∧ p2) → p1)) ∧ True) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55534750284608981499104344829 : ((((p2 → p1) → ((True → p4) ∨ p1)) → (((p1 → (False ∨ (p4 → (p4 → (((p4 → True) → (True ∨ p1)) → p1))))) → p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165410390591881546504719973406 : ((((p1 ∨ (True ∨ ((((p4 ∨ p5) ∧ p1) ∨ p1) ∨ p2))) ∨ False) → ((True → False) → p2)) ∨ (((p5 ∧ p5) → True) ∧ (p4 ∧ (p2 ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h10 := h2 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h16 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h17 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h18 := h2 h17
              -- False on the left can always be used.
              apply False.elim h18
            case inr h19 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h20 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h21 := h2 h20
              -- False on the left can always be used.
              apply False.elim h21
          case inr h22 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h23 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h24 := h2 h23
            -- False on the left can always be used.
            apply False.elim h24
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
  case inr h26 =>
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765201981770422149981763694000 : (((p4 ∧ (((((p4 → True) ∧ p1) ∨ (p3 ∨ ((p4 ∧ (((p3 → ((p1 ∧ True) ∨ False)) → True) → p1)) ∨ False))) → p4) → (p3 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228775673352927441377877948342 : ((p3 ∨ (p3 ∧ p3)) ∨ ((p3 → p1) → ((p3 ∧ (False ∧ p3)) ∨ (True ∨ ((p2 ∧ ((p4 → (p2 → ((False ∧ p1) → p1))) → False)) → p4))))) := by
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
theorem thm_5_vars_56052415059947495247756696775 : (((((False ∧ p2) ∨ p2) → p1) ∨ (False ∧ (True → ((((((False → True) ∧ p2) → False) ∧ p3) ∧ (p5 → (False → p5))) → (p3 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51795384954147078655592842836 : (((False ∨ (((p1 ∧ p4) → p3) ∨ (p3 → (True ∧ (((p2 ∨ p1) → p2) ∨ p2))))) ∧ (p5 ∨ ((p1 → True) → ((p3 ∧ p5) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61159615837766939573668019754 : ((False ∧ ((p4 ∨ ((p2 → p5) ∧ True)) → ((((((((False ∨ p2) ∧ ((p4 ∨ p2) ∨ False)) → p2) → p4) → False) ∧ False) ∨ p3) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255988048326315962399681516392 : ((True ∨ p3) → (((False ∨ ((((((p3 ∧ (p1 → p4)) ∨ p4) → p1) ∨ p3) ∨ True) ∧ (p2 → p2))) ∨ True) ∨ (p1 ∨ (p1 ∨ (True ∧ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49623016714191200866499218761 : (((((True → ((True → True) ∧ False)) ∧ p2) ∧ ((p3 ∨ p1) ∧ ((p1 ∨ (((p2 ∨ False) ∨ p1) ∨ True)) ∧ True))) → ((True → p3) ∨ False)) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h19 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h20 := h4 h19
            -- We need to get the right conjuct of h20 based on <expert-advice>.
            let h21 := h20.right
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- False on the left can always be used.
            apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h24 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h25 := h4 h24
          -- We need to get the right conjuct of h25 based on <expert-advice>.
          let h26 := h25.right
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h29 := h4 h28
        -- We need to get the right conjuct of h29 based on <expert-advice>.
        let h30 := h29.right
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h7.left
    let h33 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h34 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h35 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h36 := h4 h35
      -- We need to get the right conjuct of h36 based on <expert-advice>.
      let h37 := h36.right
      -- False on the left can always be used.
      apply False.elim h37
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h42 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h43 := h4 h42
            -- We need to get the right conjuct of h43 based on <expert-advice>.
            let h44 := h43.right
            -- False on the left can always be used.
            apply False.elim h44
          case inr h45 =>
            -- False on the left can always be used.
            apply False.elim h45
        case inr h46 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h47 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h48 := h4 h47
          -- We need to get the right conjuct of h48 based on <expert-advice>.
          let h49 := h48.right
          -- False on the left can always be used.
          apply False.elim h49
      case inr h50 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h51 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h52 := h4 h51
        -- We need to get the right conjuct of h52 based on <expert-advice>.
        let h53 := h52.right
        -- False on the left can always be used.
        apply False.elim h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330331289215902072314509084297 : (True → (p1 ∨ ((p4 ∧ p3) → ((((p3 → (p4 → (True ∧ False))) ∨ p1) ∧ (((p2 → False) → True) → p5)) ∨ ((p2 ∨ True) ∨ (p4 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166469615592305005206796295995 : ((p2 ∨ (p3 → ((False ∧ True) ∧ (p2 ∨ (((p4 ∨ (p3 ∧ p1)) → p2) → (p4 → p5)))))) ∨ (p4 → (p2 → ((p3 ∧ p4) ∨ (p4 ∨ p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38103279125933068374371076060 : ((((p5 → ((p2 ∨ ((((p1 ∨ ((p2 ∧ p3) → (p4 ∨ p1))) ∧ (True → p4)) ∧ p2) → p5)) ∨ (p5 → p3))) → (p2 ∧ False)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317838637963414802744686458106 : (p4 ∨ (((p3 ∧ (p2 → p5)) ∨ (p5 → (((((p2 ∨ p4) → p2) → (p1 ∨ ((p2 ∧ p5) → (False ∨ p3)))) ∨ (True → False)) ∨ True))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187447962855425675318659502247 : ((True ∨ ((((True → p1) ∧ True) ∧ ((p3 ∨ p1) ∧ True)) ∨ False)) → (((p2 ∨ (True ∨ p1)) ∨ p1) → ((p5 ∧ (True → False)) → (p3 ∨ p5)))) := by
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
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h11.left
          let h14 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h15 := h12.left
          let h16 := h12.right
          -- Disjunctions on the left can always be decomposed.
          cases h15
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
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- Conjunctions on the left can always be decomposed.
            let h27 := h25.left
            let h28 := h25.right
            -- Conjunctions on the left can always be decomposed.
            let h29 := h26.left
            let h30 := h26.right
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h31 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h31
            case inr h32 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h4
          case inr h33 =>
            -- False on the left can always be used.
            apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Conjunctions on the left can always be decomposed.
            let h38 := h37.left
            let h39 := h37.right
            -- Conjunctions on the left can always be decomposed.
            let h40 := h38.left
            let h41 := h38.right
            -- Conjunctions on the left can always be decomposed.
            let h42 := h39.left
            let h43 := h39.right
            -- Disjunctions on the left can always be decomposed.
            cases h42
            case inl h44 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h44
            case inr h45 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h4
          case inr h46 =>
            -- False on the left can always be used.
            apply False.elim h46
  case inr h47 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h48 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Conjunctions on the left can always be decomposed.
        let h53 := h51.left
        let h54 := h51.right
        -- Conjunctions on the left can always be decomposed.
        let h55 := h52.left
        let h56 := h52.right
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h57 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h57
        case inr h58 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h59 =>
        -- False on the left can always be used.
        apply False.elim h59



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45749990213600099186308831086 : (((False → ((p4 ∨ (((p1 → p3) → ((p3 ∧ ((p5 → p1) ∧ True)) → (p4 → (p3 ∧ p4)))) → (p3 ∨ p3))) ∨ (False ∧ True))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138299063544859070477202485952 : ((p3 → ((((p4 ∨ (p1 → ((p3 → (p5 ∨ (p4 ∨ p2))) ∧ p1))) ∨ p4) ∧ True) ∨ ((p3 ∨ (p3 → p5)) ∨ p2))) ∨ (p2 ∧ (p4 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181481281073622399080507506895 : ((p4 ∨ (p1 ∨ (False ∨ ((True ∧ p1) → ((p3 → p2) ∨ (False ∧ p4)))))) → (p5 → ((p2 → (p4 ∨ ((p2 → False) ∧ p2))) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42292760009043126120986337092 : (((p2 ∧ (((((((p2 ∨ p1) ∧ p4) ∨ (p2 → True)) ∨ p1) ∧ ((p3 ∨ (p3 ∧ p3)) ∨ ((False ∨ p3) → p3))) ∧ False) ∨ p1)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134162340483627459542949592127 : ((((p2 → (((True ∧ (True ∧ p4)) ∧ p2) ∧ (False ∧ ((p2 ∧ p5) ∧ (p3 ∨ False))))) → ((p5 → p1) → p4)) ∨ True) ∨ (p5 ∨ (True ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219534933390210147253045694024 : ((p5 ∨ (p4 ∨ (p4 ∨ p2))) → ((p1 ∨ (p1 → (p3 → (True → ((((p2 → p4) → False) → (((True → p2) ∨ p1) ∧ p4)) → False))))) ∨ True)) := by
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
theorem thm_5_vars_231659491295670692109252195903 : (((False ∧ p5) → p2) → ((True ∧ p5) ∨ (((True → p2) → p1) → (((p5 ∨ p5) ∨ p2) → ((p3 → ((True → (p3 ∧ False)) → p2)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198470035619863395576305146670 : ((p5 ∧ (p3 ∨ (((True ∧ p3) ∨ p2) ∧ p2))) ∨ ((p2 → (((((False → False) ∧ ((p3 ∨ p2) ∧ p2)) ∨ p1) ∧ False) → p5)) ∨ (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264182069200665238756823799869 : (True ∧ (((((False → (p5 → p1)) ∨ True) ∧ p3) ∧ p5) → ((p4 ∧ (((True → (((p3 ∨ p4) → True) ∧ True)) → True) → (p1 ∨ p5))) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54834680937659525907881060044 : (((p3 → (((True ∨ (False ∧ False)) ∧ p4) ∧ False)) → ((True → ((p1 → True) ∧ (((p1 → (True ∨ p3)) → p3) ∨ True))) ∧ (p1 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616258625405020739577440559646 : (((((((((p4 → p1) ∨ p2) ∨ p5) → ((p3 → p4) ∨ False)) ∨ p5) ∨ (p3 → (p1 ∨ (((p3 ∧ False) → True) ∨ (True ∧ p1))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165599517427801862996031615744 : ((((p4 → (((True ∧ p4) ∨ p3) → p2)) → p2) → ((p2 ∨ p5) → (p5 ∨ (False ∨ p5)))) ∨ ((p5 ∨ (p1 → True)) ∨ ((p3 ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_42742658157011820746848154164 : (((True → ((p2 → ((((p3 ∨ p3) → p3) → p4) → p1)) ∨ (((p1 → False) ∨ p3) ∧ (p5 → (p1 ∧ ((p2 ∨ p3) → p5)))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148309171927047522298561862560 : (((True ∧ ((True ∨ True) ∧ (((False ∨ p5) → p4) ∨ (((p2 → False) ∨ p1) → p1)))) → ((p2 ∧ False) ∧ True)) ∨ ((False ∧ True) → (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71033190552542451834072475686 : (((((True ∨ ((p3 ∧ False) ∨ True)) → False) ∧ (((((((p1 → (True → True)) ∧ p4) ∨ p4) ∧ (p5 ∧ p5)) → p5) ∧ p4) ∨ p1)) ∧ True) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ ((p3 ∧ False) ∨ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ ((p3 ∧ False) ∨ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313073532820001946994485331771 : (p3 ∨ ((((p3 ∧ (((False ∨ (p5 ∧ p4)) ∧ p2) ∨ ((p4 ∧ p4) ∨ p2))) → (False ∨ (True → (p3 → (p1 ∧ False))))) ∧ (True ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324653120907578354599616724479 : (p5 ∨ (((p3 → p1) ∨ p3) ∨ ((p1 → (((p1 → p2) → p3) → (p5 → p4))) ∨ ((False ∧ p3) → ((p4 → p1) ∨ (False ∨ (True ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_325783061695918788368548555738 : (p5 ∨ (p2 ∨ (p1 → (((((((True ∨ p1) ∨ (True → p2)) ∨ ((p2 ∧ p3) ∧ True)) → p2) ∧ ((p3 → True) ∨ (p3 ∨ True))) ∨ p1) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644208948878431323737160099961 : ((((False ∨ (((True ∨ (p3 ∧ (False ∧ p5))) → (p1 ∧ ((p5 ∨ False) ∨ ((p3 ∨ (p3 ∧ (p2 ∧ (True ∨ p5)))) ∨ True)))) ∧ p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180799626689268278655061119078 : ((((p1 ∨ p5) ∧ p2) ∧ ((p5 → p4) ∨ ((True ∨ p3) → (p5 → True)))) → (p4 → (((True ∧ (p4 ∧ True)) ∨ p2) → ((p2 → p4) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h30
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h32
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h34 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h35
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h36 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h37
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218386887598059737321551769504 : (((p5 → p3) ∨ (p1 ∨ True)) → (((p3 ∨ False) ∨ (((p1 → p2) ∨ ((True ∧ (False → p4)) ∨ p2)) → (p4 → p5))) ∨ (p5 → (False → p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
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
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44287961717255821387576065088 : ((((((p3 ∧ (p1 ∧ (p5 ∧ (False → (p3 ∨ (p1 ∧ False)))))) ∧ p5) ∨ (p5 ∨ True)) ∧ (((p4 ∨ p4) ∧ p2) → (p3 → p5))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172289978494522538232375734584 : ((((((p5 ∧ True) ∧ (p3 → p1)) ∨ True) ∧ p2) → (p5 ∧ (True ∧ (p3 ∨ p1)))) ∨ (p5 → (p2 → ((p1 ∧ False) → (p4 → (p2 ∧ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157876129575536814334377184022 : ((((p1 ∧ (p3 ∧ ((False ∨ True) ∨ True))) ∧ (True ∧ False)) ∨ (((p3 ∨ (True ∧ True)) ∨ p4) ∨ p3)) ∨ (((p3 ∨ p3) ∨ (p3 ∧ p4)) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_37197962563490127768032963082 : (((((p5 ∧ (p5 → (True ∨ (False ∨ False)))) ∨ ((p1 ∧ (p2 → (p4 ∧ ((((True → p5) → False) → False) → True)))) ∨ p5)) ∧ p2) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184389263585364138561934628612 : (((p3 → (((p2 → (p3 ∨ p4)) ∨ (False ∨ p1)) → p2)) → p2) ∨ ((True ∧ ((p1 → True) → p1)) → ((p1 → (p3 ∨ (True → p1))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145235099841839167764740381809 : ((((((p3 ∧ p2) ∧ p4) → (p3 ∨ p5)) → p4) → (p4 ∨ ((p5 → (((p3 ∨ p2) ∧ p5) ∨ p2)) ∧ True))) ∧ (((p3 ∨ p4) ∧ False) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∧ p2) ∧ p4) → (p3 ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696280489172512930285234592783 : ((((False → ((p4 ∨ (p5 ∨ (((p5 ∧ p3) ∧ p4) → p2))) ∧ (True ∨ False))) → ((((p1 → (p4 ∨ p2)) ∨ (p1 ∧ p3)) → False) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683983148639106064344323167552 : ((((((((False → (p1 → p3)) → (False ∨ False)) ∨ (False → p1)) → (p2 ∨ (p2 ∨ True))) → p5) ∨ (p5 ∧ ((p3 ∨ (False → p1)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179391725190477167250053105251 : ((p3 ∨ (((p2 ∧ ((p3 ∧ p5) ∨ p2)) ∧ p1) ∧ (p3 ∧ (p4 → p5)))) ∨ (((False ∧ True) → ((p4 → p4) ∧ (True ∨ p4))) ∧ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3197958263172961816634855875 : ((p3 ∧ p1) ∨ (p2 → ((p5 → ((((p1 ∧ p2) ∨ p3) ∨ True) ∧ ((p5 → p4) ∧ (p5 → (True ∧ ((p5 ∨ False) ∧ p3)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166406413474864217842159393819 : ((p1 ∨ (((p4 → (((p4 → (p1 ∨ False)) → (p4 ∧ (p4 ∨ True))) → False)) ∨ False) ∧ p3)) ∨ (p5 ∨ ((p5 ∧ ((True → False) ∨ True)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191535732852505924978870008115 : ((p1 ∧ (((((True ∧ p2) ∧ p3) ∨ p5) → p2) ∨ p1)) ∨ ((((p4 → (p3 ∨ (True → (False → (p4 → False))))) ∨ True) ∧ p3) → (p4 ∨ True))) := by
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
theorem thm_5_vars_118140073679008282142460802102 : ((False ∨ (((((p4 ∨ ((p4 ∧ p3) ∧ p4)) → False) → p5) → ((False ∨ p1) → p3)) ∧ ((p2 ∧ ((p5 ∧ p5) ∧ p2)) ∧ p5))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133790335663260756384945943849 : (((((False ∧ p3) ∧ p4) ∨ ((p3 → (p3 ∨ p1)) → ((p1 ∨ False) ∨ (p4 → ((p2 ∧ False) ∨ (p4 ∨ p1)))))) ∧ p2) ∨ ((False → False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140940021065487952463346110202 : (((((p3 ∨ (p1 → (p5 ∨ False))) → (p2 ∧ p2)) → p4) ∨ ((p1 ∨ p1) ∧ ((((p3 ∧ p3) ∧ p5) ∨ p5) ∨ p5))) → (p4 → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h11.left
          let h14 := h11.right
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h20.left
          let h23 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256338401510852811793225425507 : ((False ∨ p2) → ((p2 → ((p1 ∨ (((True ∧ (p4 → True)) → p5) → False)) ∨ (p1 ∧ (p4 ∧ ((False ∧ p1) → ((p4 ∧ p5) ∧ p2)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190274217880188358546424281795 : (((((p3 → p5) → ((False ∧ p1) ∨ p1)) ∨ False) ∨ p1) ∨ ((((((True ∨ p4) ∧ ((True ∧ False) ∧ p2)) ∧ p3) ∨ (p3 ∨ p1)) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113113225741716743822361745394 : (((False → (((((((True ∧ (p5 ∧ p2)) ∨ (p5 ∧ (p5 → False))) ∧ (False → p5)) → p5) ∨ p4) ∧ p4) → (p4 → False))) → p3) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226025260516593625980618321089 : (((p4 ∧ p4) ∨ p2) ∨ (False ∨ ((p5 ∨ p2) ∨ (((p4 → False) → ((False → p3) ∨ (((p2 ∨ p5) → p5) → True))) ∨ (p5 → (p4 ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205185283350038781220099593040 : (((p3 ∨ (p4 → p3)) ∧ (p4 ∨ p5)) ∨ ((p4 ∨ ((p2 → True) ∨ (p5 → ((p5 ∧ (False → p2)) ∨ False)))) ∨ (((p1 ∧ p3) ∨ p1) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168474902948738783778120859325 : ((True ∧ ((((False ∧ (p1 ∨ (p3 ∨ False))) ∧ (((p5 → True) → p2) → p4)) ∧ p5) → p3)) → ((p2 ∨ (False ∨ (True → (p3 ∧ p2)))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609490537027263375620277163547 : (((((p1 ∧ (((p1 ∨ p1) ∨ (True ∧ (p1 ∨ (False → ((((True ∧ p4) ∧ False) ∧ (p5 ∧ True)) → (True ∨ p5)))))) → p3)) ∨ False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



