variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157940777524775921090940988691 : ((((False → p1) ∨ ((p2 ∧ (False ∧ p4)) → p1)) ∧ (((True → (p2 ∨ p2)) ∨ (p4 ∧ p1)) ∨ p5)) ∨ (p2 ∨ (((False ∧ p1) ∧ p2) → p3))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154170097407913687848703603113 : ((((((False → True) ∨ (False → p3)) ∨ ((p4 ∨ ((p5 ∨ True) → p3)) ∨ (p5 → False))) → p2) ∨ True) ∧ ((p3 ∧ p2) → ((p4 ∧ p1) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_2370051684764488750347461098 : (((p3 ∧ ((p4 → ((p5 ∨ p1) ∧ p3)) ∨ p5)) → (p3 → p4)) ∨ (True ∨ ((p4 ∧ (((p2 ∧ p3) ∧ False) → p4)) → (p1 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191302322600408352985301990757 : (((p2 → p2) ∧ (p5 ∧ (((False ∨ p1) ∧ p2) ∧ p5))) ∨ ((False ∧ p3) → (p5 ∨ ((True → (p4 ∧ p4)) → (((p5 → p1) ∨ p5) → p3))))) := by
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
theorem thm_5_vars_233828985851490013115272881043 : ((p4 ∨ (True ∧ p1)) → ((p2 ∨ ((p4 → ((False ∧ (p1 → (False ∨ p4))) ∧ (((p1 ∨ p1) ∧ True) ∧ p2))) ∨ True)) ∨ (p2 ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60334180328857792595323499645 : (((p2 → p1) → ((p1 ∧ ((p5 → ((((p3 → p2) ∧ True) → (((p3 → p5) → p3) → (p4 ∧ (False → p4)))) ∨ True)) → False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310524398264871476360653289766 : (p2 ∨ ((((True ∧ (p1 ∨ False)) ∧ False) ∨ p4) → ((False ∨ (p5 ∧ p3)) ∨ (((False → p5) ∧ (p1 ∨ (((p2 ∧ p3) → False) ∨ p5))) ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2656316511485045831650232949 : (((False ∨ (p5 ∨ False)) ∧ (p5 → p5)) ∨ ((p4 → (p2 ∨ (p3 ∨ (p3 ∨ (p3 ∧ ((False → p4) ∧ p5)))))) ∨ ((p3 ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136888883152447811105985867109 : (((p3 ∨ False) ∨ ((p3 ∧ (False → ((p1 ∧ (False ∧ ((p1 ∧ (p1 ∧ p2)) ∨ (p5 ∧ (p2 ∨ p1))))) ∧ p4))) → p2)) ∨ ((p4 ∧ False) → p2)) := by
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
theorem thm_5_vars_41149976910038041334815530304 : (((((p2 ∨ (True ∧ False)) ∨ ((p4 ∨ False) ∨ (p2 ∨ ((True ∧ ((False ∧ p3) → p5)) ∨ (p1 → p4))))) ∨ ((True ∨ p5) ∨ True)) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49696651764950019215672276704 : ((((p3 → True) ∨ ((((p1 ∨ (p4 ∨ p2)) ∧ p3) ∧ True) ∧ ((p3 ∨ (True ∨ (p2 ∨ (p3 → True)))) ∨ p3))) → ((p2 → p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195495739574358648089100650692 : (((False → (p2 → p2)) ∨ ((p2 → False) → p2)) ∧ (((p4 ∧ False) ∨ ((False ∨ (p5 → (False ∨ p2))) ∨ True)) ∨ ((p4 → (p1 ∨ False)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353446802662268673216025138123 : (p4 → (p1 ∨ ((p1 ∨ p1) → ((((((p1 ∨ p3) ∨ ((((p2 → p2) → p5) ∨ p3) ∧ True)) → (p4 ∨ p3)) → False) ∨ p2) ∨ (True ∨ p4))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353527081675834841517134697949 : (p4 → (p3 ∨ ((((p2 ∧ (True ∧ (p5 ∧ p5))) ∧ ((p4 ∧ (p4 ∨ (p3 ∧ (((True → False) → p1) → p4)))) → p5)) ∨ (False → True)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749286720353239587614726962065 : ((((p5 → p5) → ((True ∧ (p2 ∨ (((p1 ∨ ((False ∧ ((p1 ∧ p5) ∧ (p2 ∨ p1))) → ((p1 ∧ p5) → p2))) ∧ p3) ∧ p4))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313332905944509367713363825701 : (p3 ∨ ((p5 ∨ (((((p3 → ((p3 → False) ∧ False)) ∧ p1) ∧ (p5 → p4)) → (p1 ∧ p5)) ∨ (False ∨ ((True ∨ (True ∧ True)) ∨ p4)))) ∨ p1)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134119749244948896478993564866 : (((((((((p3 ∧ p1) ∧ p3) → (((p5 ∧ False) ∧ p4) ∧ False)) ∨ p1) ∧ p4) ∧ (False ∨ p5)) ∨ (p1 ∨ p2)) ∨ p5) ∨ ((p2 → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234262552474223282868258752828 : ((False → (True → p2)) → ((((p4 ∨ False) → ((True → (False ∨ ((p2 ∧ (False ∧ p1)) ∧ (p4 ∨ p2)))) ∨ (False ∨ (p2 ∨ p4)))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180550504021397419159982362274 : (((p4 ∨ ((p1 → True) ∧ (p5 → (p4 ∨ p4)))) ∨ ((p5 ∨ p5) ∨ p3)) → ((p3 ∧ (False ∧ p3)) ∨ (p5 → ((p4 ∧ p1) ∨ (p5 ∨ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600725871295956996358481344317 : ((((False ∧ (((p2 ∨ (p5 → (p5 ∧ ((False → (p3 ∧ False)) ∨ p3)))) ∨ (p5 → p4)) ∧ (p5 ∨ (((p5 → False) ∨ True) → p2)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136425378500198874967340639461 : (((((False → p3) ∧ p1) → p1) → (False ∧ ((p5 ∧ (((True → ((p2 ∧ p2) ∨ True)) → p5) ∧ (p3 ∨ p2))) → p4))) ∨ (p3 ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172849348312844101393123166181 : ((False ∧ ((p3 ∧ (p3 ∧ ((p2 → p3) ∧ p5))) → (p2 → (False ∧ (p1 ∨ p3))))) ∨ (((False → (p2 → (p4 ∧ p3))) ∧ (p1 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2115048026403456706971802375 : (((p2 → ((((p4 → (p4 → p3)) → p1) ∨ ((p1 ∨ p4) ∨ (True ∨ p4))) ∨ p3)) → False) → ((p1 ∧ (True ∧ (p2 ∧ True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((((p4 → (p4 → p3)) → p1) ∨ ((p1 ∨ p4) ∨ (True ∨ p4))) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257018378721843171001913629726 : ((p2 ∨ True) → ((((p3 ∨ ((p4 ∧ p1) ∨ p2)) ∨ (p1 → True)) → ((((p1 → p2) → True) ∨ (p1 ∨ p1)) ∧ p4)) ∨ ((p1 ∨ True) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68202782709368278827424393645 : ((p3 → ((p5 ∧ (((((p5 → ((False ∧ p2) → p5)) → False) ∧ (((p1 → (p2 ∧ p2)) ∨ (p2 ∧ p2)) ∧ True)) ∧ p2) ∧ False)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118750220628334650589963273996 : ((p5 ∨ ((p5 ∨ (True ∨ p3)) ∧ (p4 → (True → ((p2 ∧ (p2 ∨ True)) ∨ (p1 ∨ ((p5 ∨ (p4 → (False → p5))) ∨ p2))))))) ∨ (True ∧ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658373503100872299222561681497 : ((((False ∨ ((((((p3 ∧ (False → p3)) ∧ ((p5 → (p3 ∨ False)) ∧ p1)) → p5) ∨ p3) → p2) ∧ ((p3 ∨ True) → p4))) ∨ (p5 → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_56887657549642877575767187801 : (((p3 ∧ (False ∧ False)) ∧ (((p5 ∧ (p2 ∨ (((p1 ∨ True) ∨ (((p1 → p3) ∨ p4) → p4)) ∨ p1))) → ((True ∨ True) ∨ True)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444555375340230402961055227458 : ((((False ∨ (p1 ∨ ((p1 ∧ (p2 ∨ (p4 → (((p2 → True) ∧ ((p5 → p1) ∨ p2)) ∨ p4)))) ∨ (p1 ∨ p4)))) ∨ (False → (True ∨ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247444316554266277979287498850 : ((False ∨ p2) ∨ (True ∧ ((((p5 → (p3 ∨ (((((True → p3) ∧ p5) ∨ False) ∨ p2) → p2))) → (p4 → True)) → False) ∨ (p5 ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_647215315043736338205377700412 : ((((p3 → (p3 → ((False ∧ (((p5 → p4) ∧ p1) → (False ∧ (p4 ∨ (p1 ∧ (True ∧ p2)))))) → (p5 → ((p3 ∨ p1) ∧ p5))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150866846835294127300981868039 : (((((p1 ∧ p5) → ((p5 → (p1 ∨ p5)) → p5)) → (((p2 ∨ ((True → p4) ∧ p2)) ∨ p2) ∧ p4)) ∨ p4) → ((True → (p2 ∨ False)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p1 ∧ p5) → ((p5 → (p1 ∨ p5)) → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h3
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52367835089084434451283611258 : ((((((p3 ∧ ((True ∨ p2) ∨ p2)) ∨ True) → (p3 ∨ True)) → (p3 ∧ p3)) ∧ ((False ∧ ((p3 ∧ (p2 ∨ p5)) ∧ (p1 ∨ p5))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53515042846910018301615470837 : (((True → (p4 ∧ ((False ∨ (p2 ∧ True)) ∧ ((p3 ∨ p3) ∨ p1)))) → ((p3 ∨ (p5 → (p2 ∨ (p3 ∧ p3)))) ∨ ((p1 ∨ p1) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_116089401313028044197975464556 : ((((p2 ∨ p3) ∨ p3) ∧ (p2 → (False ∨ (((p2 ∨ p4) → (True ∨ (p3 ∨ (p1 ∧ (((False ∧ p4) ∧ p4) ∧ p1))))) → p4)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668586144620215963917384800450 : ((((((p3 ∧ p4) → ((((False → (p3 ∧ p5)) ∨ p2) → (p3 → p5)) ∧ ((p5 ∧ False) ∧ (False ∨ True)))) ∧ p3) ∨ (p2 ∨ (False → p3))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167050272283709046572036380920 : ((((((p4 ∨ (False → ((True ∧ p2) ∨ p1))) → ((p3 ∧ False) ∧ p3)) → p5) ∨ p3) ∨ False) → (((p2 → (p1 → (p3 ∨ False))) ∨ True) ∨ p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504938723528411917288410030997 : ((((True → (p3 ∨ p4)) → ((((False → (p4 → (((p4 → False) ∨ p5) → p1))) ∧ True) → (False ∧ (True ∧ p5))) → (p2 ∨ (p4 ∧ False)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False → (p4 → (((p4 → False) ∨ p5) → p1))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172698107211272671812539751541 : (((p5 ∧ p2) ∨ (p1 ∨ (((p4 → p1) → False) ∧ (p5 → ((p3 → p5) ∧ p1))))) ∨ (False → (p2 ∨ ((p2 ∨ (p3 ∧ p3)) → (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53304041255306670728533853086 : (((p4 ∨ (True ∧ (((p5 → p3) ∨ p5) → (p4 → (p2 ∧ p1))))) ∨ ((p1 → p3) → (((((p4 → False) ∧ True) ∧ False) → p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57018125886441941365608645510 : (((False → (p3 → p4)) ∧ ((((False ∨ p3) ∧ (p4 ∧ True)) ∧ (p1 → (False ∨ (p3 ∨ (p5 ∨ (True ∧ True)))))) ∨ (True ∨ (False → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115186321986722510495404961374 : (((((False ∧ (p5 ∧ p5)) ∧ p5) ∧ (p4 ∨ (p5 ∧ p5))) ∧ ((p2 ∨ (((p2 ∨ p1) ∨ True) ∧ p3)) → ((p4 ∨ True) ∧ p4))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180657404990267807916823111065 : (((p3 ∨ ((p4 ∧ True) ∨ (p2 → True))) ∨ ((p2 → False) ∨ (False ∨ p3))) → ((p1 → (p3 ∨ (((p1 ∨ False) → p3) ∨ (False ∨ p1)))) ∨ False)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228176302875003777672819619162 : ((p5 ∧ (p2 ∧ True)) ∨ ((p2 → ((p5 ∧ p2) ∧ False)) ∨ ((p5 ∨ ((((p5 ∨ p3) → (p4 ∨ True)) ∨ (p1 ∧ p1)) ∨ (False → p3))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39914073024780986722440750126 : (((p3 → ((p2 ∨ (((((((p2 → True) ∨ ((p3 ∨ p5) ∧ ((True ∨ True) ∨ p3))) ∧ False) ∨ True) ∨ p1) ∧ p3) ∨ p3)) → p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232360830620765090177099944867 : (((p4 → p4) → False) → (False ∧ ((((((p5 ∨ p3) ∧ (((p2 → p5) ∧ False) → p1)) → False) ∧ (p1 → p1)) → False) ∧ ((p4 ∧ p4) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h11
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h14
  -- False on the left can always be used.
  apply False.elim h16
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h18
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h17
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113059128867702940016851239868 : (((p2 ∨ ((((p2 → False) ∨ True) → (False → ((True → p2) ∧ (p4 ∨ (p4 ∧ p1))))) ∨ ((p3 ∨ p2) → (p4 → p5)))) → p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197640812559169147515525964312 : ((((p3 → (p3 ∧ p5)) ∨ p2) → (p2 ∧ False)) ∨ (True ∧ (((False → (p5 ∧ ((p5 → p1) ∨ p2))) → True) ∧ ((p2 ∧ p1) → (p4 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336222921264472543194574826049 : (p1 → (((((p4 ∨ (((((False ∨ p4) ∧ p2) → p5) → (p3 ∧ (p4 ∧ (True ∧ p5)))) ∧ True)) ∧ p4) ∧ p2) ∨ ((p3 ∧ p1) ∧ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657655374623101906657332141478 : (((((p3 ∨ True) → (((((p5 ∨ False) ∨ p5) → ((((p2 → p1) → True) ∧ (p5 ∨ (p3 ∨ False))) ∨ p3)) → p1) ∧ p5)) ∨ (p4 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_60705761329846972814909557318 : ((True ∧ (((p1 → (False ∨ (True → (p2 ∧ p4)))) → False) ∨ ((p5 → (p2 → p5)) ∨ (p3 ∧ (p1 ∨ ((False ∧ (p2 → p1)) ∨ p4)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185441121436942908289628728033 : ((False ∨ ((p1 ∨ (p3 ∧ p2)) ∧ (p3 ∧ (p2 ∧ (p3 → True))))) ∨ (((p3 ∧ ((p4 ∨ (True ∨ ((False ∧ True) → p3))) ∨ p2)) ∧ False) → p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h3
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72072787480386250818481299189 : (((p5 ∨ (((p5 ∨ ((p2 ∨ (((True ∨ False) ∨ p1) ∧ (p2 ∨ ((((p1 ∨ True) ∨ True) ∧ p5) ∧ p2)))) ∨ True)) → p5) ∨ p5)) ∧ p1) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : (p5 ∨ ((p2 ∨ (((True ∨ False) ∨ p1) ∧ (p2 ∨ ((((p1 ∨ True) ∨ True) ∧ p5) ∧ p2)))) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354684677122567507819878122326 : (p5 → (((p5 ∧ (p2 ∧ (True → (p3 ∧ (p5 ∧ ((p4 ∧ (p2 → (False ∧ (p1 → p4)))) → (p5 ∧ (True → p2)))))))) ∧ (p3 → p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258058017037870045663579675824 : ((p4 ∨ p2) → (((True ∨ (True → p5)) ∧ ((p5 ∨ (True → (False ∧ p5))) → p2)) → (((p2 ∧ p2) → (False ∧ (p1 → (p3 ∧ p1)))) → p4))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (p2 ∧ p2) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h8
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∧ p2) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h14
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53670205013483794449148031562 : ((((False ∧ p5) → ((p3 → (True ∨ p2)) ∨ (p2 ∨ p1))) ∧ (p3 → (p4 ∨ ((p5 ∨ (p2 → (p1 ∧ (p2 → (p5 ∨ False))))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133896741730634190512584360605 : (((False ∨ (p3 ∧ (p5 ∨ ((True ∧ ((p4 ∧ (p1 ∨ p4)) ∨ (((p5 ∧ True) ∧ p4) → p1))) ∧ (p2 ∧ True))))) ∧ p3) ∨ (False → (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112237087908259385585651618667 : (((p2 ∨ (p1 ∨ (((p4 ∧ p5) ∧ (p4 → ((True ∧ False) ∨ (((p2 ∧ p4) → (p3 → (True ∧ p4))) ∧ p3)))) → False))) ∨ True) ∨ (p3 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358366864323936548975219365777 : (p5 → (True → ((p3 ∨ ((p5 ∨ p2) → False)) → (((p5 ∨ (p3 ∨ (p1 ∨ p5))) ∧ p1) → (((p4 ∨ p4) → (p3 → (p2 ∨ True))) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713949912626291839936886054096 : (((((p5 ∨ (p2 ∧ (False → p4))) ∨ p1) → (((p2 ∨ (((p4 → p1) ∨ p5) ∧ True)) → p5) ∨ (((True → True) ∧ False) → (p1 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258157464066216126972531771109 : ((p4 ∨ p4) → (((((p1 ∨ p1) → (p2 → p5)) ∧ (False ∧ ((p5 → (True → p2)) ∨ False))) ∨ ((p3 → ((p5 ∧ p4) → True)) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113643109347899859819806772864 : (((((((p1 → (((p2 → p3) ∨ (((p2 ∧ p4) ∧ p4) ∧ False)) → (p1 ∧ False))) ∧ p3) → False) → p5) ∧ p1) → (p3 ∨ p1)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116245559389232779809936981157 : ((((True → True) → p2) ∨ (p4 ∨ (((((((p5 → (p2 ∧ False)) ∨ p4) ∧ (False → True)) ∨ False) ∧ p1) → (p3 ∧ p4)) ∨ p5))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_525264572194348599903832011995 : (((True ∧ (False ∨ ((p1 ∧ ((p4 ∧ (p3 ∨ (p1 → (((p2 → p3) → False) ∨ True)))) ∨ (p1 ∨ (p1 ∧ ((p3 ∧ False) ∨ p4))))) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310461844021936240506952592565 : (p2 ∨ ((((p2 ∧ True) ∧ False) → (p5 → p4)) ∧ (((((p1 ∨ ((p1 ∨ p3) → p2)) ∨ (False ∨ ((False ∧ p5) → p5))) ∨ p2) → False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (((p1 ∨ ((p1 ∨ p3) → p2)) ∨ (False ∨ ((False ∧ p5) → p5))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h8
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47340756481032578914408921406 : ((((p2 ∨ p4) ∧ (True ∧ (((p3 ∨ ((p2 ∨ ((True → p4) → p4)) ∨ p3)) → p1) ∧ (False ∧ (p4 ∨ (p1 → p2)))))) ∨ (False ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57398935653345111471508915955 : (((False ∨ (p1 ∨ p1)) ∨ (((False → (p3 ∧ (p2 ∨ True))) → p5) → (((p3 ∨ (p3 ∧ p2)) ∨ (p4 ∨ (p2 ∨ (False ∨ p2)))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_516572357723307048052828452087 : ((((p4 → p1) ∨ (p1 → (((((p5 ∨ (True ∧ p2)) ∧ p2) ∨ ((p3 ∨ p5) ∧ ((p4 → (p4 ∨ True)) ∨ (p3 → p2)))) → p4) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115318329090773060857858957800 : ((((True → (p1 ∧ p3)) ∧ (((True ∨ p2) → p2) → False)) → ((((True ∨ p3) → (p1 ∨ True)) ∧ (p2 ∨ (p1 → p3))) ∨ p1)) ∨ (p1 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299851671465107838415738890291 : (False ∨ ((p5 ∧ (False ∨ (((p5 ∨ (p3 ∧ p5)) ∨ (True ∨ p5)) ∧ (((False ∧ p1) ∨ (((p2 → (p5 ∨ p2)) ∧ p5) ∨ p5)) → False)))) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h10 : ((False ∧ p1) ∨ (((p2 → (p5 ∨ p2)) ∧ p5) ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h11 := h7 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h15 : ((False ∧ p1) ∨ (((p2 → (p5 ∨ p2)) ∧ p5) ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h16 := h7 h15
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h19 : ((False ∧ p1) ∨ (((p2 → (p5 ∨ p2)) ∧ p5) ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h20 := h7 h19
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h22 : ((False ∧ p1) ∨ (((p2 → (p5 ∨ p2)) ∧ p5) ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h23 := h7 h22
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49138296257461822354198878833 : ((((False ∨ (((True ∨ ((p1 ∨ True) → False)) ∧ p4) ∨ True)) ∧ (p5 ∧ (True ∧ (((True ∨ False) ∧ p3) ∧ False)))) ∨ ((p2 ∨ p4) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179207546554067097023138087322 : ((p4 ∧ (((p1 ∨ ((((p1 ∨ False) → p1) → False) ∨ p5)) ∧ p1) ∨ p5)) ∨ ((p5 ∨ (p2 → True)) ∨ ((p5 ∧ (p1 ∧ (p3 → p1))) ∧ p2))) := by
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
theorem thm_5_vars_259390716759940684427576347557 : ((False → p3) → ((((p3 ∧ (p3 ∨ p4)) → (p5 ∧ (((p2 → (p2 ∨ p3)) ∨ p1) ∨ True))) → False) ∨ (p3 → ((False ∨ (p2 → p1)) → p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117471027185469353868593972613 : ((p1 ∧ (p3 ∧ ((((False ∧ (p4 → (p4 ∧ (p3 → p5)))) ∧ p2) ∨ ((p5 ∨ ((p3 → p1) ∧ True)) → (p1 ∧ False))) ∨ True))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659631473254658304913436501116 : ((((((p5 ∧ ((p5 ∨ p2) ∧ (p3 ∧ (p4 → p4)))) → (p1 → ((((p2 ∨ p3) ∨ p5) ∧ (p5 → False)) → p3))) ∧ True) → (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353414692018188643145596768746 : (p4 → (p1 ∨ ((p1 → (((((p4 ∧ p5) ∧ True) → (p4 ∧ (p5 ∧ (p4 → p2)))) → ((False ∨ p2) ∧ (True ∨ (p2 ∧ p2)))) ∧ p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256975774065857981109150075833 : ((p1 ∨ p5) → ((p3 ∧ p3) ∨ ((p4 ∨ (p2 → p2)) ∨ ((p3 ∧ False) → (((((p4 → False) → (True ∧ (p2 ∧ p4))) ∧ p3) ∨ p4) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135476760338218282398775497502 : (((((p1 ∧ p4) ∨ (False ∧ ((p4 → False) ∨ p3))) ∨ (((p4 ∧ False) ∨ p1) ∨ (p2 → p5))) → (True ∧ (True → p2))) ∨ ((True → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38885857654577936870540627219 : (((((p5 ∧ False) ∨ p5) ∨ ((((p1 ∧ p5) → ((p4 ∨ p1) ∧ False)) ∨ p2) → ((((p4 ∧ p2) → p3) ∨ p1) → (p3 → p3)))) ∧ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783276899168276619436877027705 : (((p3 ∨ (((((p1 ∨ p2) ∧ ((False ∨ (((p5 ∨ p4) → (p5 → True)) ∧ True)) ∧ True)) ∧ p5) ∧ False) ∨ ((False → p3) → (True ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55348136628877759037941912503 : (((p1 → ((p3 ∨ (p1 → p1)) → p3)) ∨ ((p3 ∧ (p4 → ((p3 ∨ True) → p4))) → ((((False ∧ (p4 ∨ p5)) ∧ p2) ∧ p5) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45523062006143913738402756495 : (((p1 ∨ ((((True ∨ p3) ∧ False) ∨ p1) ∧ ((((((False → p4) → p5) ∨ (p2 ∨ p1)) ∧ (p5 → (p4 → p3))) → p4) → p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147770764150623656970204802707 : ((((True ∧ p2) ∨ (p1 → (((p3 ∨ p2) → (p2 ∨ False)) → ((p4 ∧ True) ∨ (p2 ∧ (p4 ∧ False)))))) → p2) ∨ (p2 ∨ (True ∧ (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_1767624823008924795253336425 : ((((p3 ∧ p3) ∨ (((((p2 → p5) → p1) → p5) ∧ ((p2 ∧ (False ∨ p4)) ∨ (False ∨ p4))) → p5)) ∨ True) ∨ ((p5 ∧ p1) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62512490761074073523402103750 : ((p3 ∧ (p3 ∧ ((p2 → ((p3 ∧ (True ∧ (p4 ∨ ((p4 → p2) ∧ (p5 ∧ p5))))) → p5)) ∨ (((p5 ∨ p1) ∧ (False ∧ p2)) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135678723512543175421408794689 : (((((((p1 ∨ (p5 ∧ p5)) ∧ (p3 ∧ p3)) ∧ (p5 ∨ False)) → False) ∧ p5) ∧ ((((p4 ∧ p1) ∧ p1) ∨ p4) ∨ p3)) ∨ (p4 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632541493889056176462115198645 : (((((p5 ∨ ((p2 → (False ∨ p5)) ∧ ((p3 → ((True ∨ p3) ∨ True)) ∨ ((True → (True → p1)) → (p2 → (False ∨ p3)))))) → p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348218385011596157547436169341 : (p3 → ((p3 → False) → (((((((((p1 ∨ p4) ∧ (p1 ∨ p4)) ∨ False) ∧ p3) → (p5 ∧ True)) → (p1 → p3)) ∧ p1) ∨ p4) ∨ (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54901392195428876858967908940 : ((((p2 ∨ ((p5 ∨ p1) ∨ p1)) ∨ False) ∧ ((p2 → True) → (False → ((((((True ∨ p1) ∨ p5) ∨ False) → p3) ∨ (True ∨ p1)) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352667654412770122770617142513 : (p4 → ((False ∨ False) ∨ (p4 → ((((p1 → p5) ∨ (p1 → (p5 ∧ (p3 ∧ p2)))) ∧ p1) ∨ (False ∨ ((p5 → ((p2 ∨ False) ∨ p5)) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262299266933069603063419559967 : (True ∧ ((((p5 ∧ p2) → (((p2 ∧ True) ∧ (p2 ∨ (p4 ∧ True))) → (p4 ∨ p5))) → (p3 ∧ ((p4 → p1) ∧ ((p4 ∨ False) ∨ p3)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115745551350263418552166777708 : ((((True ∧ True) → (p1 ∧ (False → p2))) → (p1 → (p4 ∨ ((p2 ∨ p4) ∧ (((False ∧ (p4 ∧ p5)) ∨ True) ∨ (p4 ∧ False)))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623931140679915223507282419832 : ((((p2 ∨ (((p2 ∧ p5) ∧ (False ∧ ((False → (((False ∨ p3) ∨ False) ∨ (p4 ∨ (p4 ∧ (p2 ∨ (p2 → p1)))))) → p1))) ∧ p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307712816555169357303116805786 : (p1 ∨ (p2 → (p4 ∨ ((p4 ∧ (((p5 ∨ True) ∨ (((p4 ∧ (p3 ∧ p5)) ∨ p1) → (p4 → p1))) ∧ (True ∧ ((p5 ∨ p5) ∧ p3)))) ∨ True)))) := by
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
theorem thm_5_vars_121869882372811463623901615909 : ((((p4 → p2) → (((False ∨ ((p1 → (False ∧ True)) → (p2 ∨ True))) ∨ (p2 ∧ (p1 ∧ p2))) ∧ (p5 ∧ (True ∧ p3)))) → p3) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40947729288343511017184590540 : (((((((((False → (p4 ∧ False)) ∧ p3) ∧ p1) → ((p5 → (p4 → (p3 → p2))) ∧ True)) → p5) ∧ (False ∧ p5)) ∨ (p4 ∧ p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231940231749872572272854572614 : (((p1 ∨ True) → p2) → (((p3 → (p4 ∧ False)) ∨ ((p1 ∨ ((p5 → ((p5 ∧ False) ∨ (p4 → ((False ∨ p1) ∨ True)))) → True)) → p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p1 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336340473254700952287940920771 : (p1 → (((False ∧ p5) ∧ ((False ∧ p4) ∧ (p5 ∧ (((((True ∨ (False → ((p5 ∨ p1) ∨ (False ∨ p4)))) ∧ p4) ∨ True) ∧ p4) ∨ p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234275090953136172372065472752 : ((False → (p1 → p3)) → (True ∧ ((p5 ∨ (((p2 ∨ (p2 → (True ∧ True))) ∧ (p5 ∨ (False → False))) → p4)) ∨ ((p4 ∧ p4) ∨ (True ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215932645224477743402558386352 : ((p3 ∨ (p5 ∨ (p5 ∨ p5))) ∨ ((((((False ∧ p2) ∧ p2) ∨ p5) ∨ (p4 → p1)) ∨ (((True ∨ (p1 ∨ (False → p5))) ∨ p4) → True)) ∨ p4)) := by
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



