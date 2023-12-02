variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193602782300476700297361745846 : (((p4 → p1) → (True ∨ (p5 → ((p1 ∨ p3) ∧ p2)))) → (((p1 ∨ (True → p5)) → p5) ∨ (p2 → (False ∨ (p5 → (False → (True → False))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347795840416985328929834653386 : (p3 → ((p1 ∨ (p4 ∨ False)) ∨ (((((p4 ∧ (p4 ∧ p3)) ∨ p2) ∧ p3) ∧ (p2 ∨ p2)) ∨ (True ∨ ((p3 ∧ (p1 ∨ p3)) ∧ (p1 ∧ p5)))))) := by
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
theorem thm_5_vars_342018306416447337178640308761 : (p2 → ((p5 ∨ ((p3 ∨ ((p2 ∨ (False ∨ ((False → (p3 ∨ True)) ∨ True))) → ((p1 ∨ (p3 ∨ p3)) ∧ p5))) ∨ p2)) ∨ ((True → True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87039361763159657076659812366 : ((((((True ∨ p2) ∨ p2) ∧ (p5 ∧ False)) → False) → (((False ∨ ((p5 ∧ ((p4 ∧ p1) ∨ (p1 ∧ p1))) ∧ (p3 ∧ p4))) → True) ∧ False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ p2) ∨ p2) ∧ (p5 ∧ False)) → False) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h8 := h5.left
        let h9 := h5.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h5.left
        let h12 := h5.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- False on the left can always be used.
      apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595616648570976845564123106238 : (((((((((p1 ∧ False) ∧ True) ∧ p4) → p2) ∨ ((p2 ∨ p1) → p2)) → (p5 ∧ ((((p3 ∨ (p2 ∨ True)) ∨ True) ∧ p4) → p4))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224345148470520470065642864048 : ((False → (True → p4)) ∧ ((p5 ∨ (p1 → (p5 → (((True ∨ p1) ∨ (p3 → (p1 → (((p1 ∨ p1) ∨ p3) ∨ True)))) → p3)))) ∨ (p4 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114360666782235994246177766667 : (((((True ∨ ((p4 ∨ p4) ∨ p4)) ∧ ((p4 ∧ (False ∧ (True → (False ∨ p3)))) ∨ p2)) ∧ False) ∨ ((True → (p3 → p3)) ∨ p3)) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119053721828622913610816828560 : ((p1 → ((True → (((p3 ∧ (True ∧ ((False ∨ (p2 ∨ (False ∨ p5))) ∧ p1))) ∨ (((p2 ∧ p2) → p1) ∨ False)) → False)) ∨ True)) ∨ (p5 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700586800501972131038669248885 : ((((False → ((p5 ∧ p4) ∨ (True → ((p2 ∨ p5) ∧ (p2 ∨ p3))))) → ((p2 → p5) ∨ ((((p1 → False) ∧ p4) ∧ (True → p1)) → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61849288775523041200720405408 : ((p2 ∧ (((p4 ∨ ((((False → p4) ∧ p2) ∧ (p3 ∨ False)) ∧ ((p2 ∨ True) ∧ (p1 ∧ (True → p2))))) ∨ (p5 → (p2 → p4))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196505453986672752968483840683 : ((p2 → (((p2 → (p4 ∨ p1)) ∨ p4) → p2)) ∧ (((p5 ∨ (p4 ∨ (((p2 ∧ p5) ∨ ((p1 → p2) ∨ False)) ∨ True))) ∨ p5) ∨ (False → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113834538107165577043952262587 : (((p1 ∨ (((p3 ∨ p4) ∨ p5) → ((p2 → ((p4 ∧ (p1 ∨ ((p2 ∨ (p3 ∧ p2)) → p2))) → p2)) ∧ p1))) → (p2 ∧ p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184260655316405486389909449341 : ((((p1 ∨ (((p5 ∧ p3) ∧ p3) ∧ p4)) ∧ (p2 ∨ p3)) → False) ∨ (p5 → ((((p3 → (p4 ∧ p2)) ∨ True) ∨ p4) → (p1 ∨ (p1 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134078356989259526324497515161 : ((((((True ∨ (p3 ∨ ((p5 ∨ (p4 ∨ p1)) → (p1 ∨ p2)))) ∨ p5) ∧ ((p5 ∧ False) ∨ (p2 → p5))) → p1) ∨ True) ∨ ((True ∨ False) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234583093433857494919894070364 : ((p3 → (False ∨ p2)) → (((p5 ∧ ((p1 → p4) ∨ False)) ∧ (((p4 → (False ∧ p2)) → p3) ∧ (p5 ∧ ((True → (p5 ∧ p3)) ∨ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55254163538811545521837851753 : ((((p5 ∧ p1) ∨ (False ∨ (False ∧ p1))) ∨ ((p5 ∨ (True ∨ (p2 ∧ (p3 → ((p2 → (p3 ∨ (p5 ∨ False))) ∨ p1))))) ∧ (False → False))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616520861043230298298529403507 : (((((p1 → ((p1 ∨ False) ∧ (((p4 ∧ (p3 ∧ p5)) → p5) → p3))) → (((p1 ∧ (p4 ∨ p3)) ∧ p3) ∨ (p2 ∨ (p4 → p4)))) ∨ p4) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_9308721961026840739044504063 : (((((p2 ∨ (p5 ∧ (p5 ∨ p4))) ∨ p1) ∨ (p1 → (p2 ∧ ((p2 → (((p4 ∧ (True ∧ (p2 → False))) → p2) → p4)) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158696009695309854375646825673 : ((p2 ∧ (p5 ∧ (p2 → ((((True ∨ (p3 ∨ p1)) → (p5 → False)) ∨ (p4 → p5)) ∨ (p2 ∧ p2))))) ∨ ((False → (p2 → p4)) ∨ (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52813932543607955382398377096 : ((((p4 ∨ (p2 ∨ (p3 → (p3 → p4)))) → ((True ∧ p5) ∧ (p4 ∨ p5))) → ((True ∨ (p2 ∧ True)) → ((True → p4) ∨ (False ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51521260300228753274254822527 : ((((p3 ∨ p3) ∨ (p4 ∨ (((((p1 ∨ True) → (p4 ∧ p4)) ∨ (p3 ∧ p2)) ∧ p3) → p2))) → ((False ∧ ((p5 ∧ False) ∨ False)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_248719131965637896546571288486 : ((p3 ∨ p2) ∨ ((p3 → False) → (p5 ∨ ((((p2 ∧ (True ∨ True)) ∧ p5) ∧ (p4 → p5)) → (((((True → p2) → p1) ∨ p2) ∨ p1) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351265800284993303891100799554 : (p4 → ((True → (p1 ∧ ((p3 ∧ False) ∨ (((p3 ∨ p5) → (((False → False) ∨ ((True ∧ p5) ∨ True)) ∧ p4)) → p2)))) ∨ ((p2 → True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358050111575927873970028987363 : (p5 → (p1 ∨ ((p2 ∨ ((p3 ∧ p2) ∧ ((((p1 ∨ ((True ∧ (p1 ∧ p4)) ∧ p1)) → (p4 → True)) ∨ p4) ∧ p4))) ∨ (p5 ∨ (p4 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168279617428834226276709993935 : (((p2 ∧ p3) ∧ (p3 ∧ ((True → (p3 → (p5 ∨ p4))) ∨ (p5 ∧ ((p4 ∧ p1) ∨ p5))))) → (False ∨ ((p5 → (p5 ∨ p5)) → (p4 ∨ p3)))) := by
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
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698559404679599886752159844272 : (((((p5 ∨ ((p2 ∨ p2) ∨ p4)) ∨ (((p4 → True) ∧ p3) ∧ p3)) ∨ (p1 → ((False ∨ (p5 ∨ (True ∨ (False ∨ (p1 ∨ p3))))) ∨ p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16598786358959318308373141654 : ((((((((True ∧ p4) ∨ False) ∨ ((((p2 ∧ (p3 ∧ p5)) ∨ p1) ∨ (p3 → p4)) ∨ p2)) ∨ True) ∧ p4) ∨ p5) ∨ (True ∨ (p3 → False))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64848445182768704230583345963 : ((p2 ∨ ((p4 → ((p4 ∨ p3) ∧ ((((p5 ∨ True) ∧ (p2 → p2)) ∨ p5) ∨ (((p1 ∨ (True → p5)) ∨ False) ∨ (False ∨ False))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127091592561898148593339468295 : ((False ∨ ((p3 ∧ p1) ∧ (p5 ∧ (((p5 → p5) → ((p1 ∧ (p3 → False)) ∨ p4)) ∧ (((True ∨ True) → p4) → (True ∨ p3)))))) → (p4 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h14 := h10 h12
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h21 =>
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h24.left
    let h28 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708333123613778491768883002332 : ((((((p5 → (True ∧ (p5 ∧ p2))) ∨ p2) ∧ p3) → (((p3 → (p3 → (((False ∧ p4) → ((False ∨ p4) ∧ p2)) ∧ p5))) ∨ p2) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56522631073896414136787681526 : (((p5 ∧ (p1 ∨ (p1 → p1))) → (((((p2 ∧ False) ∧ p2) ∨ (p5 ∨ p1)) ∨ (p5 ∨ ((p4 → (True → p2)) ∧ (p1 ∨ False)))) ∨ False)) ∨ p5) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111085831128577951469480003753 : ((((p3 → ((False → (p2 → ((p4 → False) → p4))) ∨ (p5 ∧ p5))) ∧ ((False ∨ (((True ∨ p3) ∧ p2) ∨ p1)) ∧ p1)) ∧ p4) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43668124866015088377913294215 : (((((p1 ∧ (((p2 ∧ ((p3 → ((False ∨ p5) ∧ (p3 → p3))) ∨ p5)) ∨ p2) ∧ p4)) → (True ∧ (p5 ∧ (p5 ∧ p1)))) → False) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950378013795675152758907044481 : (((((p5 → p1) → p4) ∧ ((((p1 → False) → (True ∨ (p1 → p4))) ∨ p2) → (((p1 → (False ∨ (p3 ∨ p5))) ∨ (p2 ∨ p4)) ∧ p1))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 → False) → (True ∨ (p1 → p4))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722063609360285789250510487624 : ((((p1 → (False → (p3 ∧ p2))) → (False ∨ ((False → ((p4 ∨ ((True ∧ p4) ∨ (p5 ∨ p1))) ∧ (True → p2))) ∧ (False ∨ (p1 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156742728004676896060938995932 : (((((True ∨ False) ∨ p5) ∧ ((p3 ∧ (((p2 → p5) → (p2 ∧ p5)) ∨ False)) ∧ (p3 ∨ False))) ∧ p4) ∨ (True ∨ ((p3 ∨ (p3 → p4)) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670040529395458647989396004304 : ((((((False ∧ p3) ∨ (((False ∧ p5) → p1) → p1)) ∨ ((((p1 ∧ (p1 ∧ p2)) ∨ (False ∧ p3)) ∨ True) ∨ p5)) ∨ ((p1 ∧ p4) → p5)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671585495212589229016460927981 : ((((p5 → (((p4 → ((p4 ∨ p4) ∧ (p4 → (False ∨ p2)))) ∨ (p5 → ((p2 ∨ True) ∧ p4))) ∨ (p5 → p1))) ∨ (p1 → (p4 ∨ True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158349689765405085017001381319 : (((p5 ∧ p1) ∧ (p2 → (((((p4 ∧ p1) → p5) ∨ True) → ((True ∧ True) → (p2 ∧ p1))) → p5))) ∨ ((p1 → (p3 → (True → p1))) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47919381206858502213536696634 : ((((True ∨ (p5 → ((p3 ∨ p4) ∧ (True ∨ ((p2 → (p1 ∨ ((p1 ∧ (False ∧ p5)) ∧ p5))) ∨ False))))) → (False → True)) → (p2 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214899480139234856048221236882 : (((p4 → False) ∨ (p1 ∨ p4)) ∨ ((((True ∨ p3) ∨ (p2 → ((p5 ∧ False) ∨ p2))) → (((True ∧ (True ∧ p3)) → p2) → (p5 → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178305772216307106557186606879 : (((((True → p5) ∧ (False ∨ (False ∨ (p1 ∧ p2)))) ∧ p1) ∨ (True ∧ p5)) ∨ ((p2 → ((p1 ∧ p2) ∨ (p3 → ((True ∨ p2) → True)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113307682907366059650616544619 : ((((((p2 → True) ∨ True) → p3) ∨ (((p1 ∨ p1) ∨ ((p5 ∧ (True → ((True → p5) ∨ p2))) ∨ True)) → p5)) ∧ (True ∧ p5)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112067430004053863085645339540 : ((((True → p3) ∧ (p3 ∧ ((p5 ∧ ((p1 ∨ ((p3 ∧ (False ∨ p2)) ∨ (False ∧ ((p4 → False) → p4)))) ∧ p5)) ∨ False))) ∨ True) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134230258796646143353718591283 : ((((((p1 ∧ p1) → True) ∧ p4) ∧ ((p4 ∨ (p1 → (p5 ∧ p5))) ∧ (((p1 → False) ∧ (p4 ∧ p1)) ∨ p4))) ∨ True) ∨ (p5 ∧ (p5 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213190167050542202434729506707 : ((((p4 ∨ p1) ∨ p2) ∧ False) ∨ (p4 ∨ (((p1 ∧ p1) → ((p3 ∨ True) ∧ (p4 ∨ p3))) → (p3 ∨ (True ∨ (p1 ∨ (False ∨ (p5 → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_302012075466854539975556424149 : (False ∨ (True ∧ (((((p1 ∧ (p1 ∨ False)) → True) ∧ (True ∨ ((p1 ∧ p3) → p2))) → (((True → p4) ∧ (p2 ∧ (False ∨ True))) → p2)) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59161146002159768696924276455 : (((False ∨ p2) ∨ (((p2 ∨ False) ∧ (((False ∨ (p4 ∧ (p4 → p1))) → (p2 ∨ p3)) ∨ p3)) → (p5 ∨ (((p3 ∨ p2) ∧ p5) ∨ p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227886152673899018501004040077 : ((p2 ∧ (True → p2)) ∨ ((p3 ∨ ((True → p4) ∧ (p2 ∧ ((p1 → (p5 ∨ (p4 ∨ p3))) ∨ ((True ∧ False) ∨ p1))))) ∨ ((p4 ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729824147945690412535406301347 : (((((True ∧ p4) → p1) → (((((True ∨ False) ∧ p4) ∧ ((p2 → p2) ∧ (False ∨ (p3 → p1)))) ∧ (p5 ∨ (True → (p2 ∧ p5)))) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244089891723943831140327112170 : ((True ∧ p3) ∨ ((p2 ∨ (False ∧ ((False ∨ (p4 ∧ ((p1 ∧ p3) ∨ p5))) ∨ p1))) ∨ (True ∨ (p5 ∧ (p2 ∨ (((p3 ∨ p4) ∨ p3) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54896973624055752912133420020 : ((((p1 ∧ (p5 ∨ (p5 ∨ p2))) ∨ True) ∧ (p5 ∨ (p4 ∨ ((p1 ∨ (((True → p5) ∧ (p5 ∨ True)) → (True ∧ p5))) ∧ (True ∨ True))))) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53227794881745279812416415420 : ((((p2 ∨ (False ∨ (True ∧ p2))) ∨ (((p2 → p3) ∧ p1) ∧ True)) ∨ (p4 ∨ ((p5 → ((p5 ∨ p4) → p5)) ∨ ((p1 → False) ∨ p4)))) ∨ p5) := by
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
theorem thm_5_vars_198449923657281393134726952767 : ((p5 ∧ (((p2 → False) ∧ (False → False)) → p2)) ∨ ((((p4 ∧ p3) → (p2 ∧ (((p4 ∨ p4) → p5) ∨ True))) → p5) ∨ (p4 ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_328455243526971124223905836227 : (True → ((((p1 ∧ p3) ∨ (p5 ∨ (p2 ∨ (True ∧ p3)))) ∨ ((p1 ∧ (p4 ∧ (p4 ∧ False))) ∨ p1)) → (p4 ∨ (p4 ∨ (p5 → (p2 ∨ True)))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114848359866185990631971812657 : ((((p1 ∧ ((False → (p1 ∧ False)) ∨ (((True ∧ p3) ∧ p4) ∧ p5))) ∨ p1) ∨ (p4 → ((((p5 → p5) → p5) ∨ p1) → False))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40197178545289045565613738361 : (((((p2 ∨ (False ∧ p5)) → (p3 ∨ ((True ∨ (p5 ∧ p3)) ∧ ((p3 ∧ p3) → ((p2 ∨ p5) ∧ ((p1 ∨ False) ∧ p1)))))) ∧ p3) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107355112586118971064020442078 : (((p1 ∨ (p2 ∨ p4)) ∨ (((p3 ∧ (p1 → p1)) → ((p4 ∧ False) ∨ (False ∨ p3))) ∧ (p3 → ((p2 ∧ p5) ∨ (True ∨ False))))) ∧ (False → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259178961778803898181863548662 : ((False → True) → (p2 → ((((p2 ∧ p5) ∧ p3) → p4) ∨ ((((p2 ∧ (p4 → True)) ∧ (p2 → (p5 ∧ (p3 ∧ p4)))) ∧ (p1 ∨ p5)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h16 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h17 := h7 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42273772361190289857561578171 : (((p1 ∧ (((p1 → p3) ∨ p1) ∨ (((p1 ∧ ((False ∨ True) ∨ (p4 → (p2 ∧ p1)))) ∨ (False ∧ ((p1 ∧ True) ∨ False))) ∧ False))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773712564650148253286669837016 : (((False ∨ ((((((p3 → p2) ∧ p2) → (((p1 ∨ (p2 → p1)) ∨ (p3 → (p3 ∨ True))) ∧ (p2 → (True ∧ p1)))) → p2) ∨ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143882217659633914114960589059 : ((((((((p1 ∧ p2) ∧ p1) ∨ (p3 ∨ p1)) ∨ (p1 ∨ (p4 → p5))) ∧ True) ∨ ((True ∧ True) ∨ p5)) ∨ p4) ∧ (p1 ∨ ((p2 ∧ p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207488088368050964081901086913 : (((p3 → (p4 ∧ (p4 ∨ p1))) ∨ p2) → ((p5 ∨ ((p5 ∧ p2) ∧ (False ∨ p3))) ∨ (((p3 → p3) → p5) ∨ ((p4 → p4) → (p5 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785334431415634938120391774911 : (((p4 ∨ ((((((False ∨ (((p4 → p4) → p2) → (p4 ∨ p5))) ∨ (p5 ∧ (p5 ∧ (p1 → True)))) ∧ (p1 ∨ p3)) ∧ False) ∨ p2) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_47042411229039682078885615191 : (((((p5 ∧ (True → ((True ∨ False) ∧ (p1 ∨ p2)))) → ((p4 → (p5 ∧ (p2 ∧ True))) → (p4 → False))) ∧ (p1 ∨ p5)) ∨ (p5 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37230977856317470228720104703 : (((((p2 ∧ p2) ∨ (((p3 ∧ (p1 → (((p1 ∧ (p2 → p5)) → True) → p4))) ∧ p1) ∨ (((p1 → p3) ∨ p2) ∧ False))) ∧ p5) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2194274212632043014532704691 : (((p3 → (True → p5)) → ((p2 → p3) ∧ (p2 ∨ (((p4 ∨ p2) ∨ p5) ∧ p5)))) ∨ ((False ∧ p4) ∨ (False → (p1 ∧ (p2 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776441923608830591776567329013 : (((p1 ∨ ((((((p3 ∨ ((((True ∨ p5) ∧ False) → p1) → p1)) → ((p2 ∧ p3) → False)) ∧ p3) ∨ (p1 → (p1 → p5))) → p4) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_137475397596592367843643607145 : ((p4 ∧ (p3 → ((True ∨ (p3 ∨ ((p2 ∨ True) → ((False ∧ p4) ∧ p5)))) → (True ∧ (((p1 ∨ p5) ∨ p4) ∧ False))))) ∨ (True ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612522873983758143318791112801 : ((((((((p2 ∨ p2) ∧ p1) ∨ (((True ∨ (((p5 → (p4 ∧ True)) → False) → (True → p5))) → p1) → p2)) ∨ True) ∨ (p4 ∧ p5)) ∨ p1) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48796636833442239806049917078 : (((False ∧ (p2 ∨ ((p4 ∧ (p5 ∧ p4)) → (p3 → (p2 ∧ ((((p5 ∧ p5) → p1) → True) → (p4 → False))))))) ∧ (p5 → (p5 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310513795139789574343612020919 : (p2 ∨ ((p3 ∨ (p2 ∨ ((True → False) ∨ p3))) ∨ (((((p2 ∨ p4) → p5) ∧ (p4 ∨ p5)) → (False ∧ (p4 → (True ∨ p4)))) → (False → p2)))) := by
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
theorem thm_5_vars_313935973519346580784995083531 : (p3 ∨ ((((((False ∧ p1) ∨ True) ∨ p3) → (p3 ∧ (p1 → ((p4 ∨ p3) ∧ ((False ∧ p3) ∧ ((p4 ∧ True) ∧ p2)))))) ∨ True) ∨ (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67458806159025052847898146830 : ((p1 → (((p2 ∧ p4) ∧ (((True → p2) ∨ ((p3 ∧ (p2 ∨ p2)) ∨ (p5 ∧ p2))) ∨ (p3 ∨ p4))) ∨ ((False ∨ (p2 ∧ p4)) → p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60667151082068331876688338768 : ((True ∧ (((((p3 ∧ ((p4 ∧ (p3 → p4)) ∧ True)) ∨ ((p2 ∧ False) ∨ p3)) ∧ p1) ∨ p4) ∨ (p3 ∨ (p5 ∧ (p3 ∨ (p3 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53173349980034785708805058608 : ((((((p4 ∨ p1) → (False → (p4 → True))) ∧ (p2 → p1)) → p5) ∨ (((((p5 ∧ (p1 ∧ False)) ∨ p2) → p5) ∧ True) ∨ (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147190716380480522523284025931 : (((p4 ∨ ((p4 ∨ p1) ∧ ((p2 → (p3 ∧ (True ∧ (p5 ∧ (p1 → p5))))) ∧ ((p5 → p4) ∧ p1)))) ∧ p1) ∨ (p2 → (p4 → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61485206791551247316943548175 : ((p1 ∧ ((((p2 ∧ p2) ∨ p1) → (True ∧ (p3 → (False ∧ (((p3 ∧ ((p1 → p4) ∧ p1)) ∨ p1) ∧ p1))))) ∧ (p4 → (p5 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41683664704020183830606793777 : ((((p5 ∧ ((p3 → p2) ∨ (p2 ∧ p5))) ∨ ((((((p5 ∨ p5) → p2) ∨ (p4 → (p2 ∨ p4))) → (p5 → p1)) → p3) → p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119552402862393142139208480418 : ((p5 → ((p4 ∧ (p1 → ((False → (((p3 ∨ (p5 ∨ p1)) → (p1 ∧ p4)) → p1)) → (p2 → True)))) → (False ∨ (p3 → False)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192724462333256244510903903297 : ((((True ∨ (p3 ∨ p4)) → ((p5 ∧ p4) → p5)) → False) → (((p4 ∨ True) → ((p4 ∨ (p5 ∨ False)) → (((p5 ∨ p3) ∧ p5) ∨ p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ (p3 ∨ p4)) → ((p5 ∧ p4) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115837587887172654269316779005 : (((p1 ∧ (p5 → (p1 → p1))) ∧ ((((p4 ∨ p3) ∨ (((p5 → False) ∨ True) → p4)) ∧ (p4 ∨ ((p5 ∨ False) ∨ p3))) → False)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165242444911711513251376980144 : (((p5 ∧ (p3 → ((p2 → ((p1 ∨ (p3 → p3)) → True)) → (True ∧ False)))) ∨ (True ∧ True)) ∨ (((p4 ∧ p5) ∧ ((p5 → p2) ∧ True)) ∨ p5)) := by
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
theorem thm_5_vars_302022453114598407302445577664 : (False ∨ (True ∧ (((p4 ∨ (((p2 ∧ p5) ∨ (p4 ∧ (((((False ∧ (True → p2)) ∧ p2) → p3) → p3) ∧ p3))) ∨ p3)) ∨ p4) ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679684698937843899417348119413 : (((((((p5 → ((True → p3) ∧ False)) → ((((p5 ∨ p5) ∨ (p5 ∧ True)) ∨ p3) ∨ p3)) ∨ p3) ∨ p3) → (((p1 ∨ p2) ∨ True) ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685213598493958216535785499469 : ((((True → ((p1 ∧ (p5 ∧ (((p5 ∨ (p5 → ((False ∧ p2) ∨ p2))) ∨ p5) ∨ p4))) ∨ True)) ∨ ((True → p1) → ((p2 ∨ p3) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779126334006053478472306921733 : (((p2 ∨ (((p2 ∧ ((True ∧ (True ∧ (p1 ∨ (p5 → p3)))) ∧ (p1 ∨ (((p5 ∧ p2) → (p5 → p4)) → (p2 → p3))))) ∨ p5) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307260887344104502398571227396 : (p1 ∨ (p2 ∨ ((((((p3 → False) ∧ p5) ∨ p4) → ((p2 ∨ p2) ∨ (p3 ∧ (p5 ∧ p1)))) → p1) ∨ (((False ∧ p5) → p4) ∨ (p5 → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114654221524434888217008253096 : ((((((p4 ∨ p3) ∧ (p5 ∨ False)) → (False → p2)) → ((p2 → (p3 ∨ True)) → p1)) ∨ (((p1 ∧ True) → p3) ∨ (p1 ∧ p3))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927688071485889302508489733212 : (((((p2 → (((p4 ∨ False) ∧ False) → (False ∨ p4))) → p2) ∧ ((p1 → (p5 ∧ p5)) → (((p1 → p1) → p5) → ((p3 ∨ p5) → True)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (((p4 ∨ False) ∧ False) → (False ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244112247443341039240174521909 : ((True ∧ p3) ∨ (p2 ∨ (((((p4 → (((True ∧ (p1 → p3)) ∧ p1) ∨ p2)) → False) → (p2 ∧ False)) ∧ p3) ∨ ((p4 ∧ False) → (False ∨ True))))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60055475329891694485181553281 : (((p2 ∨ False) → (((((p4 ∨ (p3 → p1)) ∧ (p4 ∧ p5)) ∨ p2) → p2) → (False ∧ (False → (p2 → ((True → p2) → (p4 → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40870005166391736144871990574 : (((((p5 → ((p2 ∧ (((((True ∧ False) ∨ p1) ∨ p2) → (False ∨ ((p4 → True) ∧ True))) ∨ True)) → p1)) → False) ∧ (False ∨ p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225144934417932021634341368916 : (((p3 ∧ p1) ∧ p5) ∨ (p2 → (((p1 → (((p1 ∧ p3) ∨ False) → (p3 ∨ (True ∧ p1)))) → (p1 ∨ p4)) ∨ (p5 ∨ ((p5 ∧ p4) → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340736197943140371179225916186 : (p2 → (((((p1 ∧ (((p2 → (((False → p4) ∧ False) → p2)) → ((((True ∧ p5) ∨ p5) → p3) → p2)) ∧ p1)) → p4) → p5) ∨ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183953319507415438332242473550 : (((p5 ∨ (((p1 ∧ p1) ∧ (p4 ∨ (p2 → p3))) → p4)) ∧ p4) ∨ (((p1 ∧ (((p3 ∧ (True ∨ False)) ∧ (p2 ∧ True)) ∧ p4)) ∧ p5) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h9.left
    let h14 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84736060695113574169579974812 : ((((p2 ∧ (p2 ∨ (p4 ∨ (False ∧ (False ∨ True))))) ∧ ((p1 → p3) → True)) ∧ ((True ∧ (True → (p2 ∧ False))) ∧ (p5 → (p3 ∨ p3)))) → False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180084300684326348559348905768 : ((((((p2 ∧ (False ∧ ((p3 → p5) → p4))) ∧ p5) ∨ p3) ∧ p1) → p1) → (p5 ∨ ((False ∧ (p5 ∧ p3)) → (((p3 → p3) ∧ p4) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4677311217026306353096674731 : (p5 → (p3 ∨ (p1 → (((p1 ∧ ((True ∧ ((p2 ∧ p3) → p4)) → (((True ∧ True) ∧ False) ∧ p3))) ∨ (p4 ∨ False)) ∨ (False → False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149938713340078403327838288525 : ((p3 ∨ ((p5 → p3) → ((p3 ∧ ((((p3 ∧ p4) ∨ (p3 → False)) ∧ p3) ∧ (False → (False ∨ True)))) ∨ True))) ∨ ((p1 ∧ p3) ∧ (p2 ∧ p4))) := by
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



