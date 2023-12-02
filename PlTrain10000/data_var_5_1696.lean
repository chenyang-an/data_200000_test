variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227846139173234022081065577964 : ((p2 ∧ (True ∨ p1)) ∨ (((p1 ∧ (p3 ∧ True)) ∨ p4) ∨ ((((False → False) → p4) ∨ p2) ∨ (((p1 → ((True → True) ∨ False)) → True) ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54273710761910272338657863968 : ((((p5 → (p5 ∧ p2)) ∧ ((p4 → p5) → p4)) ∧ (p4 ∨ (p4 ∨ (((((p5 ∧ (True ∨ p5)) ∧ p1) → p1) ∧ p2) ∧ (True ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_74696828252396481378476625492 : (((p3 ∧ ((p3 → (((p5 ∨ (p2 → p1)) ∨ (((p4 ∨ p2) ∨ ((p5 → True) → p4)) → p1)) ∧ (p4 ∨ (p3 ∧ False)))) ∨ p4)) ∨ p4) → p4) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68713121762404131843605849963 : ((p4 → ((p4 ∧ (False ∧ ((p2 ∨ False) ∧ (((((True ∧ ((p3 ∧ False) → p5)) ∧ p5) ∧ p1) ∧ False) ∨ p4)))) ∧ ((True → p3) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305492366099584129980124843281 : (p1 ∨ (((p5 ∨ ((p3 ∨ False) ∨ ((p4 ∧ ((p2 ∨ p2) ∧ p1)) ∧ False))) ∨ p5) ∨ ((p2 ∨ p5) ∨ ((p2 ∨ (True ∧ (p4 ∨ p1))) → True)))) := by
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
theorem thm_5_vars_38726152066486201780915537428 : (((((True ∧ (p3 ∧ True)) → (p3 ∧ p1)) → ((p1 → ((p3 ∧ p5) ∧ (((p3 ∨ p1) → p4) ∧ p1))) ∧ ((p5 → p4) ∨ p5))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40047413525775142860886287899 : ((((((((p1 → ((p3 ∨ (p3 ∨ (p1 ∧ (True → (p1 ∧ p5))))) ∨ (p1 ∧ (p4 ∧ p2)))) ∧ True) ∧ p2) ∧ False) ∨ p2) ∧ p4) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49460055222459156174897087188 : ((((p3 ∨ (((p2 ∨ (((False ∨ (p5 → (p3 ∨ (p2 ∧ p4)))) ∧ p4) ∧ (False → False))) ∧ False) ∧ p5)) ∨ True) → (p4 ∨ (p1 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54959230474867104524680332696 : ((((p4 ∧ (p2 ∨ p5)) ∨ (p3 → p3)) ∧ (((True → p5) ∨ ((p4 ∧ p5) ∨ (p2 → ((p5 ∨ ((p5 ∧ p4) → p2)) ∧ p2)))) ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257610202776498681504198877423 : ((p3 ∨ p2) → (((p4 ∧ ((p2 ∧ (((p4 → (p3 ∧ p1)) → p1) ∨ True)) ∨ (((False ∨ p2) ∧ p4) ∧ (True ∧ p5)))) ∨ (p3 ∧ p1)) ∨ True)) := by
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
theorem thm_5_vars_193829224852167968742218136665 : ((p5 ∧ (False ∨ (((p5 ∧ True) ∧ (True ∧ False)) → p3))) → (((True ∨ (p1 ∧ p3)) → False) → ((p4 ∧ p1) ∨ (((p5 ∨ True) ∧ False) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ (p1 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179214104482873378157043563864 : ((p4 ∧ ((p3 ∨ (p2 ∨ ((p1 ∧ False) ∨ (p4 → p3)))) ∧ (True ∧ False))) ∨ ((True → ((((True ∧ p5) ∨ False) → (p3 ∨ p2)) ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254285416195954642398067718282 : ((p2 ∧ p3) → (((p1 → ((((p4 → p5) ∧ (False → p4)) ∨ (p4 → p5)) → (p2 ∧ (True ∧ p1)))) → (p5 ∧ p4)) ∨ (p4 → (p4 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792727616266987148390818570563 : (((True → ((True ∧ (p3 ∧ (False → p5))) ∨ (((((((p5 ∨ ((True → p2) ∧ p2)) ∨ (False → p2)) ∨ p4) ∧ p5) → p1) ∨ True) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49140423542211027872777644055 : ((((((p2 → (p4 → (p4 ∧ p3))) ∧ p1) ∧ (p5 → p3)) ∨ (((True → ((p5 → p2) ∧ p2)) → p5) ∧ True)) ∨ (True ∨ (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198764846768615655222861285307 : ((True → (p3 ∧ ((p2 ∧ p5) ∧ (p2 → p3)))) ∨ ((p5 ∧ (True ∨ ((p3 ∨ (((p3 ∨ ((p3 → p3) → p5)) ∧ p5) ∨ p1)) → True))) → p5)) := by
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
theorem thm_5_vars_185268902326502521405522801395 : ((p1 ∧ (p5 ∧ ((p2 ∨ ((p3 ∨ p3) ∨ p1)) ∧ (True ∧ p3)))) ∨ (p2 ∨ (((p3 ∨ ((p3 ∨ (p3 → p3)) ∨ False)) → (p3 ∨ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157771572893738091355368424177 : (((((((p4 ∧ p4) ∨ p5) → (p1 ∧ (False ∨ p4))) → p3) ∧ p4) ∨ (True ∨ (False ∨ (p4 ∧ p5)))) ∨ ((True → ((p2 ∨ p5) ∧ p5)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52807030691719204019913004553 : ((((p3 ∨ (p5 → ((p2 ∧ True) → p2))) ∧ (p4 ∧ ((p4 → p2) ∨ False))) → (p5 → ((p2 ∨ ((p4 → False) ∨ p5)) ∨ (p1 → True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185571003945174030250728771309 : ((p4 ∨ (p2 ∨ (True → (p4 → (p5 ∧ ((p2 ∨ p5) ∨ p2)))))) ∨ (((((p1 ∨ (False → p2)) ∧ p1) → (p1 ∧ p2)) ∨ False) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637332439438300550251279148701 : (((((True ∨ (True → (p3 → (False → ((p1 ∨ p5) → (p5 ∨ p3)))))) → ((((((p1 ∧ False) ∧ p3) ∧ p5) → True) ∧ False) ∧ True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46399076173012019415655571266 : ((((((p4 → p1) ∨ (p3 → p1)) → (True ∧ p1)) ∧ ((p3 → (p4 ∨ p4)) ∨ ((p2 → p3) → (p3 → (p5 → True))))) ∧ (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51864720222672209738377872919 : ((((((((p4 ∧ (p1 ∨ (p1 ∨ False))) ∧ p2) ∨ p2) → p1) ∨ (p5 → False)) ∨ p1) ∨ (((((False ∧ True) ∧ p5) ∨ True) ∧ False) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3974471875427779391711173247 : (p1 ∨ ((((((False ∨ False) → p1) → ((((p1 → (False ∧ (p5 → False))) → False) → p2) → p3)) ∧ (p1 ∨ p1)) ∨ p5) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336078418145115672766081255860 : (p1 → ((((False ∨ (False ∨ (((p3 ∧ ((((p5 → p4) → p2) → p1) → p2)) ∧ p4) ∧ ((p3 ∨ p1) → p3)))) ∨ (True ∧ p1)) ∧ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41399772483002239037409688874 : ((((True → ((((p4 ∧ p1) ∨ (((p3 ∨ p3) ∨ True) → p4)) ∨ p3) ∧ p4)) ∧ ((False → (p3 ∧ (p4 ∨ (False ∧ p4)))) ∨ False)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64723996932414625602515154947 : ((p1 ∨ (p4 → (False ∧ ((p3 ∨ False) → ((False → p3) → ((p4 ∨ ((((p1 → True) ∨ p2) ∨ ((p5 ∨ p1) → p1)) ∧ p1)) ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683843144827276049394452389618 : ((((((p2 ∨ p5) ∧ (p4 ∨ ((p3 → p4) ∨ ((True ∨ (p4 → p4)) ∨ (p3 ∨ p4))))) ∨ False) ∨ ((True ∨ (p3 ∧ (p3 → p3))) ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_68206402571104996550169728873 : ((p3 → ((p4 ∨ (p5 ∨ ((p4 ∨ p3) → ((p5 ∨ (p2 → (((False ∨ p5) ∧ p2) ∨ True))) ∨ (p5 ∨ ((p3 ∧ p4) ∧ p5)))))) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388338410400343512185722776382 : (((((p4 → (((p5 ∧ (p5 ∨ ((p1 ∨ ((p1 → False) → p5)) → p3))) → (p2 ∨ p2)) ∨ True)) ∨ (p4 → ((p1 ∨ p1) ∨ p3))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207575704934911258290458552726 : ((((True ∨ (p2 ∧ p5)) ∨ p3) → p1) → ((p2 ∨ (((True ∧ True) → p4) ∨ (p5 ∧ (False ∨ ((p3 ∨ p3) ∧ p2))))) ∨ (p4 ∨ (p4 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810150054469622484349679229730 : (((p5 → ((((True ∨ p4) ∧ (p2 ∨ (((p4 ∨ (p4 ∧ (p5 → True))) ∧ True) ∧ p5))) ∨ p4) ∨ (p1 ∨ (True → (True ∧ (True ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_550687480950062357453136602080 : (((p1 ∨ (((((((((p4 ∨ p3) ∨ p5) ∧ p1) → (p1 ∨ p2)) ∨ p5) → p2) ∨ (False → (p3 ∨ p4))) → p3) ∨ ((False ∧ p1) → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_941991280797432421323245538858 : ((((((True → p2) ∨ False) ∧ True) ∧ (False ∨ ((((p2 ∧ p5) ∧ p3) ∨ (p3 ∧ p3)) → ((((p1 → False) ∨ p5) ∧ (p1 → True)) ∧ p3)))) → p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112149590725072596260620760873 : (((p1 ∧ (p5 ∨ (p4 ∧ (((p1 → p5) → p1) ∨ (True → (p3 ∨ (((False → p1) ∧ p2) ∨ (p3 → (False → p3))))))))) ∨ p3) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927084563587400686312397942634 : ((((True → ((((p2 ∨ ((p3 ∧ p2) ∨ p4)) ∨ True) ∨ p1) ∨ True)) → (p4 ∧ (((p1 ∧ p2) ∧ (False ∨ (p2 ∧ (True ∨ False)))) ∨ False))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((((p2 ∨ ((p3 ∧ p2) ∨ p4)) ∨ True) ∨ p1) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198689938834991006777253985011 : ((p4 ∨ (p3 ∧ (((p4 ∨ p5) ∨ p4) ∨ p4))) ∨ (p3 → ((((p2 ∨ (p2 ∨ p5)) → (p5 ∨ False)) → (((p5 ∨ p3) ∧ p1) ∨ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184317174613911845764992693411 : ((((p1 ∧ p2) ∨ (p3 → ((p2 ∧ False) → (False → p1)))) → p3) ∨ (((p1 ∧ False) ∨ (False ∧ p4)) → ((p2 → (p3 ∧ p3)) ∧ (False ∧ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340055605607521247134901532735 : (p1 → (p2 → ((p4 ∨ ((p2 → p2) → p2)) ∧ ((p2 → (((p5 ∨ False) ∨ False) ∧ (p5 ∨ ((p4 ∧ p4) → ((p3 → True) ∧ p1))))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147594218976023047754892547930 : ((((((p3 → False) → ((p2 ∧ (p1 → (((p4 ∨ (p2 → p4)) → False) ∧ p2))) → p4)) → p5) ∨ p1) → p4) ∨ (p3 ∨ (False ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_66607386707349495620691000784 : ((True → ((((False → (False ∧ ((p2 ∨ p1) ∨ p2))) ∨ (False ∧ ((p3 → p3) ∨ p2))) → (p3 ∧ p1)) ∨ (False → ((p3 → p1) ∨ p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190295414990509446630381504401 : (((((False ∧ (p5 ∧ p4)) → (p2 ∨ p4)) → p4) ∨ p5) ∨ ((False ∧ True) ∨ (((False → ((p5 ∧ p5) ∧ ((False → True) ∧ True))) ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249032289735025867794498502485 : ((p4 ∨ False) ∨ (p3 ∨ ((p5 ∨ ((p2 ∨ p3) ∨ p3)) ∨ (p3 ∨ ((p2 ∨ p3) ∨ ((True → p3) → (p1 → (p2 ∨ ((p4 ∨ p2) ∨ p1))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701461786971525019281571543653 : (((((p1 ∨ (p2 ∨ p1)) ∧ ((False ∨ p2) ∨ (False → p2))) ∧ (p5 ∨ (((((p4 ∨ ((p5 ∨ p2) ∨ p3)) → False) ∨ True) ∧ False) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321237593267105768239139529017 : (p4 ∨ (p4 ∨ ((((p1 → p3) ∧ ((p1 → ((((p4 ∨ True) → ((p2 ∧ (True → p5)) ∧ p3)) ∧ p5) ∧ False)) ∧ p1)) ∧ (False → p4)) → p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172042475782066875096457582948 : (((True → ((False → False) ∧ (p4 ∧ ((p2 → (p4 ∧ p4)) → p5)))) ∨ (p3 ∨ False)) ∨ (p1 → (((False → (p2 ∨ p3)) ∨ p2) ∨ (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317146774912377195171959858456 : (p3 ∨ (p5 → (p4 → (((p4 ∧ (((((True ∨ True) ∧ p3) ∧ True) ∧ p3) ∧ p5)) ∧ ((p2 ∨ ((p2 ∨ (p3 ∨ p4)) ∨ p5)) → p2)) → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : (p2 ∨ ((p2 ∨ (p3 ∨ p4)) ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h17
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h20 : (p2 ∨ ((p2 ∨ (p3 ∨ p4)) ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h21 := h5 h20
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62736748167482685863724399270 : ((p4 ∧ (((((((p1 → (p2 ∨ p4)) ∨ ((p2 ∨ (True → p3)) ∨ True)) ∧ p3) ∧ (p3 → (p4 ∨ p2))) ∧ p2) → p5) ∨ (p3 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133648796574919567507356952560 : (((((p5 ∨ False) ∧ (((False ∧ (((p1 ∧ p5) → p5) → p1)) → (False ∧ (p1 → p4))) → p4)) ∧ (p5 ∧ p2)) ∧ True) ∨ ((False ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147996012359230423591866253054 : (((((p4 ∨ ((((True ∧ p3) ∧ (False ∧ p4)) → ((p4 → p5) ∧ p4)) → p3)) → p2) → p5) ∨ (True ∨ True)) ∨ ((p2 ∨ (p5 ∨ p2)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_866481889123232013652368165755 : (((((p4 ∧ (p5 ∨ p1)) ∨ (p4 ∨ ((((p4 ∨ (p2 ∨ ((p1 ∧ p3) → ((p2 ∨ p4) ∨ p3)))) ∨ (p1 → True)) → True) ∨ True))) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (p5 ∨ p1)) ∨ (p4 ∨ ((((p4 ∨ (p2 ∨ ((p1 ∧ p3) → ((p2 ∨ p4) ∨ p3)))) ∨ (p1 → True)) → True) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112939309831342209154680654627 : ((((p1 → p1) → (((False ∨ p3) → (True → ((p5 ∨ ((p4 ∨ (p1 → p3)) ∨ p3)) ∨ (p1 ∨ (False ∧ False))))) ∧ p1)) → p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320052960185514229860376600521 : (p4 ∨ ((p5 ∧ (p5 ∨ p5)) ∨ ((p4 ∨ (p3 ∨ (True ∧ (((p2 → (True ∨ p4)) ∨ ((True ∨ (p3 ∨ p4)) ∧ False)) → True)))) ∧ (p5 → p5)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114561557225154243769150564650 : (((((False → (False ∨ (p4 ∨ p2))) ∨ ((p4 → False) ∧ (p5 → (p3 ∨ p3)))) → p4) ∧ (((p3 ∧ p2) ∨ p3) → (p2 → p5))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311955677461801122686662390351 : (p2 ∨ (p3 ∨ ((False ∧ (p1 ∧ p4)) ∨ (((((True ∨ True) ∨ (p3 ∧ p3)) ∨ (p3 → (((p2 ∨ p5) → p1) ∧ (p5 ∧ p2)))) ∨ p1) ∨ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178353888419133794017066560662 : (((p1 ∨ (((p1 ∨ False) ∨ (p4 ∨ p3)) → (p4 → p3))) ∨ (p4 ∨ p4)) ∨ ((False → p1) ∨ ((False → (True → (p3 ∧ p5))) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_166671264966173736041862417038 : ((p2 → ((False ∨ (False ∨ ((p3 ∧ p2) ∨ (((False ∨ (p1 → p1)) ∨ p4) ∧ p3)))) ∨ p4)) ∨ ((p2 → p2) ∨ ((p4 ∧ (True → p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736475326694185231478607400713 : ((((p1 → p1) ∧ (((p2 → p5) ∨ (p2 ∧ True)) → (((False ∨ True) → (p4 → ((p3 ∧ (((p3 → p4) ∨ p3) → p3)) ∨ p4))) ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184848119199418532736848098752 : (((p1 → (p5 ∧ (p3 ∨ True))) → (p5 ∧ ((p1 → False) ∨ p5))) ∨ (((p3 ∧ (False ∨ True)) ∧ p1) ∨ ((((False ∨ p3) ∨ True) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609969805460253393380282507275 : (((((p5 → (p4 ∨ ((p4 ∨ p3) → ((p5 → (False ∧ (p2 ∧ (p1 ∧ p5)))) → (p4 ∧ (False ∨ ((p1 ∧ p5) ∧ p4))))))) ∨ True) ∨ p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_52585701720092079992112363609 : ((((p3 → (((p4 ∨ True) → (p4 ∧ p3)) → False)) ∧ (True → (p5 ∧ p4))) ∨ ((p5 ∨ (p3 ∧ (p1 → (p2 ∧ (True ∧ p1))))) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42520680618568621331830796632 : (((False ∨ (p4 ∨ ((True ∨ (p1 → True)) ∧ (((((p1 → p4) → p1) → p3) ∨ False) ∧ ((p2 → p1) ∧ ((p5 ∧ p5) → p5)))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458124656948290426819382314860 : (((((False ∧ (p1 ∧ p1)) ∨ ((True ∧ ((False → p1) → ((p1 ∨ False) ∨ False))) ∨ (False → False))) ∨ (p2 → ((p1 ∨ p3) ∧ (p5 → p5)))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754487812703165873688311016670 : (((False ∧ (False ∧ (((((((p5 ∧ (p1 ∧ p3)) ∧ True) ∨ p3) ∧ ((p2 → p5) ∨ (p2 → p2))) ∨ ((p5 ∧ p4) → p3)) ∧ p4) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263155097499419874151620401296 : (True ∧ ((p2 ∧ (((((p1 ∨ (p5 ∧ (p3 → ((p1 ∨ (p5 → (p4 ∧ p3))) ∧ p4)))) ∨ p4) ∧ (True ∨ p2)) ∨ p2) → p5)) ∨ (p3 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205272722569779858963053495763 : ((((False → True) → False) ∨ (p5 ∧ p5)) ∨ (False → (((p4 ∨ (p5 ∧ p1)) → (((((False ∧ False) ∧ (p3 → p1)) → p2) ∧ False) → p5)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192672345714472081764560900736 : ((((True ∨ (p1 ∧ ((p1 ∧ p2) ∧ p1))) → p2) → p5) → (p4 → ((((p3 ∨ True) ∨ False) → (p3 → (p2 → False))) ∨ ((p1 ∨ p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174385313425937118515564970045 : (((((p1 ∨ True) → p5) ∨ ((p3 ∧ False) ∨ p5)) ∧ (False ∨ (p5 ∧ (p5 ∧ True)))) → ((p5 → p4) ∨ ((p1 → (p4 → p3)) → (False ∨ True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622779034521954978578369102343 : ((((p4 ∧ (p3 ∨ (p4 ∨ (p1 ∧ (((((p1 ∧ (p5 ∧ p2)) → ((True ∧ (p1 ∧ p5)) → p2)) → p2) ∧ p4) ∧ (p5 ∧ p1)))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245163654208446509089773665040 : ((p2 ∧ False) ∨ ((p3 ∨ (((((((p3 ∨ p3) ∧ False) ∧ (p3 ∧ False)) ∧ p5) ∧ p3) ∧ (((p3 → p5) → (p5 → p5)) → p2)) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126607038214054804791874230987 : ((p3 ∧ ((True ∨ (p5 → (p5 ∨ (p3 → p2)))) ∧ ((((p5 → p2) ∨ p4) ∧ p4) ∨ (p2 ∨ (p1 ∧ (p4 ∧ (p5 ∨ False))))))) → (False ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
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
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h35 =>
          -- False on the left can always be used.
          apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172998916558182130844502288364 : ((p5 ∧ ((p1 ∨ ((p2 ∧ (p3 ∨ p5)) → p5)) ∨ ((p2 → p4) → (False ∧ False)))) ∨ ((True ∨ p1) ∧ ((True ∨ (False ∧ (p1 ∧ False))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591781831276085557838393543398 : ((((((((((p5 → p4) ∧ p2) → (p2 ∨ p4)) ∨ ((p2 → p3) ∧ (p3 → (p3 → p5)))) → p3) ∨ (p4 → p4)) ∨ (p4 → p2)) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161394687740525117046828154935 : ((p1 ∧ ((p4 ∧ ((False ∧ False) → (True ∨ p3))) ∧ (((p4 ∨ (False ∧ (p4 ∨ p5))) ∨ p3) ∨ p1))) → (((p4 → p5) ∨ (True ∧ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67987337294780935844361912041 : ((p2 → ((p4 ∨ p2) ∧ ((((((p3 → p2) ∨ p4) ∨ p3) → ((False ∨ p1) ∨ p2)) ∨ p3) → ((False ∨ p5) ∨ ((False ∧ p5) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45386657254766361551403122730 : (((p5 ∧ ((((False → p2) ∧ (((True ∧ ((p5 ∧ (p4 ∨ False)) ∧ ((False → p4) → (True ∨ p3)))) ∧ p4) ∨ p2)) ∧ p2) ∨ p2)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117532492179083382321094683081 : ((p2 ∧ (((p5 ∨ (p4 ∧ p2)) ∧ (((((p3 → (False ∨ p4)) → (p2 → p4)) → (p2 → p4)) ∧ p5) ∧ p4)) ∧ (p4 → p1))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305914916340000427967576480231 : (p1 ∨ (((p4 ∨ (p4 ∧ p1)) → (p2 ∨ False)) → ((p2 → ((p1 → p4) → p5)) ∨ (p1 → ((p1 → ((p5 → True) ∧ (True → p5))) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_758474426448924364521568172695 : (((p2 ∧ ((p5 ∧ (True → ((True → (((((((p1 ∨ p4) ∧ p1) ∧ p4) ∨ (True → p4)) ∨ (p3 ∧ p1)) ∨ p2) ∧ True)) ∧ True))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738089424106253501736225086420 : ((((False ∧ False) ∨ (((p4 ∨ False) ∧ p4) ∧ ((((((p4 ∨ False) → False) → ((False ∧ (True ∨ p4)) ∧ False)) ∧ (p1 ∧ p3)) → p5) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179158811962906890591453356865 : ((p2 ∧ ((p3 ∨ (((p2 ∨ p1) ∨ p5) ∨ False)) ∨ ((p4 → p5) ∧ p3))) ∨ (True ∨ (((p5 ∧ (p1 ∧ p3)) → (False → p3)) ∧ (p3 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184397503784729329734042116639 : (((p5 → (p4 ∨ ((((p2 → p2) ∨ False) → False) → p3))) → p5) ∨ ((True ∨ p5) → (p1 → ((p3 ∧ (True ∨ (p5 → p5))) → (p2 → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258461599241736432151248949257 : ((p5 ∨ p2) → (((((p5 → (True ∨ p5)) ∧ p1) ∨ True) ∧ ((((p3 ∧ True) ∨ p1) ∨ True) → ((p2 → (False ∧ (p4 ∨ p4))) ∨ True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148881010070490992333991596762 : (((((p5 ∧ True) ∨ p1) → p2) ∨ (((p2 → ((((p2 ∧ p2) ∨ p1) ∧ p1) ∧ p1)) ∨ p4) ∨ (p2 → p5))) ∨ ((p5 → True) ∨ (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709314047946415851575053357884 : (((((False ∨ p2) → (False ∧ ((p1 → p5) → p3))) → (((True → p2) ∨ (((p4 → p1) ∧ True) ∧ (False ∧ ((True ∧ p3) ∧ p1)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46916622101967839711408032504 : ((((((p5 → p2) ∨ (((p5 → p4) ∧ p2) → p5)) ∨ ((p4 ∧ p1) → ((((True ∧ p1) → False) ∧ p4) ∧ False))) ∨ True) ∨ (p2 ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691907103274801542280378651271 : ((((p2 → ((p1 → ((((p2 ∨ False) ∧ (p4 ∧ True)) ∧ False) ∨ False)) ∧ (p4 ∨ p1))) → (p5 ∧ (((True ∧ (p5 → p4)) ∨ p4) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350334694295951056829131631385 : (p4 → ((p1 → (((True ∧ (p1 ∧ (p2 → p1))) ∧ False) ∨ ((((False ∨ (p2 ∨ (True ∧ True))) ∨ (False ∧ p3)) ∧ (False ∨ p5)) ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61078203118653990420162318223 : ((False ∧ ((False ∧ (p2 ∧ (((((p3 ∧ (True ∨ p1)) ∧ p4) ∧ (p2 ∨ p1)) ∨ (p2 ∨ False)) ∧ p1))) ∧ (True ∧ (True → (p3 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172874301825873278789604346264 : ((p1 ∧ ((p5 ∨ (((((p3 ∨ p3) ∧ False) ∧ p1) ∨ False) → True)) ∧ (p1 ∨ True))) ∨ ((p2 → ((p4 ∧ ((p1 → p2) ∧ p4)) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206045910362317058958443724527 : ((p2 ∧ (p3 ∨ ((p2 ∧ p1) → p5))) ∨ ((((True → p2) ∧ p3) → (p5 ∧ ((p4 ∧ p3) ∨ p5))) ∨ ((p3 ∧ (p3 → (p5 ∧ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706343538367241902073975456309 : ((((p5 ∧ (p4 ∨ (((True ∨ True) ∨ True) ∨ p3))) ∧ (((p2 ∨ p5) ∨ ((True → ((p2 → p1) ∧ p4)) ∨ p1)) ∧ (p1 ∨ (True ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328715152228465749147900693502 : (True → ((False ∨ ((p1 ∨ p1) → ((p4 → (p1 ∧ p5)) → (p2 → False)))) ∨ (p2 → ((((p2 → p4) ∨ p2) ∧ (p5 ∧ p2)) ∨ (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40860441755541193105058200469 : ((((((p3 ∨ p1) ∨ (p1 ∨ (p3 ∨ (p5 ∨ ((((p5 → p1) ∧ False) ∨ p5) → (p5 ∧ (p1 ∧ False))))))) ∨ p5) ∧ (True → False)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657570871596515348860148068763 : (((((p5 → p1) ∨ ((False ∧ False) ∧ (p2 → (((False → p3) → p1) → (((False ∧ (p3 ∧ True)) ∧ p2) ∧ (True ∨ p2)))))) ∨ (False ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123130971886065592211111266405 : (((((True → (p5 ∧ p4)) → p4) ∧ ((p2 ∨ (False → (p4 → p2))) → (((False ∧ False) → p1) ∧ p4))) → (True ∧ (True ∧ p3))) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651088972626930242029419285918 : (((((False → ((False ∨ True) ∧ False)) ∧ ((p1 ∨ p4) → ((((p1 ∧ True) → p2) ∨ ((p4 ∧ p4) ∧ (p5 ∨ p1))) ∧ p4))) ∧ (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804692327019929276530403250603 : (((p3 → (((p3 ∨ p1) → False) ∧ (((p5 → True) → (((((p1 → ((False → p4) ∧ True)) ∧ False) ∨ p3) → False) ∧ p3)) ∧ (False → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206544119441277042343781588991 : ((True → ((p3 ∧ False) ∨ (p4 ∧ False))) ∨ (True → (p2 ∨ (p3 ∨ (((((p1 ∨ (p3 ∨ (p2 ∨ (p2 ∧ p1)))) ∨ False) ∧ False) → False) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h4
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- False on the left can always be used.
          apply False.elim h4
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42248687128247971684639561858 : (((False ∧ (p4 → (((((((p3 → p5) ∨ p2) ∧ True) → ((p4 → False) ∨ (p1 ∧ p2))) → p3) ∧ (p4 → p4)) → (False ∨ p3)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



