variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789941648474335115612484919722 : (((p5 ∨ ((p3 ∧ False) ∧ (p3 → (((((p5 → ((p4 ∧ p4) ∨ True)) ∨ p1) ∨ False) → ((True → p4) → p4)) ∨ ((True ∧ p5) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106161567780563173324723512249 : (((p4 ∨ (p1 ∧ (p4 ∨ (p2 ∨ ((p5 ∨ (p2 ∧ p2)) ∨ False))))) ∨ ((True ∨ p3) ∨ ((((False → p1) → p4) ∨ p3) ∧ p5))) ∧ (p2 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141878524254890475642472359400 : (((p1 → True) ∨ ((((p4 → (p2 ∨ True)) → ((p2 ∧ (p5 ∨ (p5 ∨ p3))) ∨ (p5 ∧ True))) ∨ (False ∨ p4)) ∧ p4)) → ((p4 → p1) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591038484326430607703055834210 : (((((p4 → (True ∧ (p5 → ((((True ∧ (p5 ∨ True)) → False) ∨ (False ∨ p4)) ∨ (((p3 ∧ False) ∧ (p5 ∧ p5)) ∨ p3))))) → p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696594879212064207724270255075 : (((((((p1 ∧ ((p4 → p3) ∨ p3)) → True) ∧ (False ∨ True)) ∨ False) ∧ (p1 ∨ (False ∧ (p3 → ((p4 → (p3 ∨ (p3 ∧ p5))) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352641092428317823397179832162 : (p4 → ((p2 ∧ p2) ∨ (True → ((p4 ∨ (True → ((p3 ∨ True) ∨ p5))) ∧ (((p5 → True) → ((p4 → (p4 ∧ (p1 → p2))) ∧ False)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172089524946397073020956722201 : ((((p1 → p3) ∨ (True ∨ ((p5 ∨ (False ∨ p5)) ∧ (p1 → p3)))) → (p1 ∧ p4)) ∨ (p5 ∨ ((p2 → (p3 ∧ p2)) ∨ ((p2 ∧ p3) → p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52252708943192195541548256000 : (((p1 ∨ ((((p2 ∧ (p4 ∧ p1)) ∧ p5) → p5) → ((p5 ∨ p2) → (False ∧ False)))) → (p3 ∨ ((p4 → p1) ∧ ((p4 ∧ p1) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193746804297982854980305447368 : ((p3 ∧ (((p1 ∨ ((p3 ∧ p2) → True)) → False) → False)) → (p1 ∨ ((((p3 ∨ (p1 ∧ p4)) ∧ (p2 ∧ (p1 → False))) ∨ True) ∨ (False ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_921732429845839783837569885667 : (((((p3 ∨ ((p3 ∨ p4) ∨ (True ∨ (((False ∧ False) ∧ p4) ∨ p5)))) ∨ True) → (True ∧ (p5 ∧ (((p5 ∨ p2) ∨ (p4 → p2)) ∧ False)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ ((p3 ∨ p4) ∨ (True ∨ (((False ∧ False) ∧ p4) ∨ p5)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68182606441991819891363713793 : ((p3 → ((((p4 → (((False → (True → p4)) ∨ ((p4 → p1) ∨ ((p4 ∨ (True ∨ p4)) ∧ False))) → p3)) → p1) ∧ (False ∨ False)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318568088397593021956614680972 : (p4 ∨ ((((((p2 ∨ p4) → (p2 ∨ p5)) ∨ (p5 → ((p1 → (p5 ∧ p2)) → (False ∧ p2)))) → ((p3 ∧ p1) ∨ False)) → p2) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726481837461964119364039323483 : (((((p2 → p4) ∨ p2) ∨ ((p5 ∧ p2) → ((False ∧ (((False ∨ (p4 ∨ ((False ∨ True) → (p1 ∨ (p4 ∨ p1))))) ∧ p2) ∨ True)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485113488408775273824904114050 : ((((p3 → (True ∨ ((p5 ∧ p4) → p3))) ∧ ((((p2 → p4) → ((p3 ∧ (True ∧ p4)) ∨ p1)) ∨ (p1 → p1)) ∧ (p4 ∨ (False → p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635132773426576937225188611395 : ((((((p5 → ((p1 ∨ True) → p2)) ∧ ((True ∨ (False → (False → ((True ∨ p5) ∧ (p5 ∧ p2))))) ∨ False)) → ((p2 ∨ False) ∧ True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93061525004931688866997318557 : ((True ∧ (((p5 → (p3 ∨ p2)) ∨ (((True ∧ p3) ∨ False) ∨ True)) → ((p5 → (p3 ∧ (((p3 → (p2 ∧ True)) → p3) ∨ p4))) ∧ False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → (p3 ∨ p2)) ∨ (((True ∧ p3) ∨ False) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48633483635052466460156744002 : ((((True ∧ (((p4 ∨ ((p2 ∨ False) → ((p5 ∧ p3) ∨ p1))) ∧ (p5 → p4)) ∧ p3)) ∨ (p5 ∨ (p3 → p2))) ∧ (p5 ∧ (p1 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58818010426489446088150107592 : (((p5 → p4) ∧ ((((((p3 → p3) ∧ p1) → (p3 ∧ p4)) ∧ ((p5 ∨ p4) ∧ False)) ∨ p2) ∧ (p3 ∧ (p5 ∨ (p3 → (False ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50151349610647499246750886994 : (((p2 → (((((p4 ∧ p1) ∨ (((False ∧ (p5 → p5)) ∨ p2) ∧ (p3 ∨ p2))) ∨ p2) ∧ p3) ∨ p5)) ∧ ((p2 ∧ p4) → (False → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641857047963975418592986894632 : (((((False → p4) → (False → ((p5 ∨ (p5 ∨ (p4 ∧ ((p5 → ((p3 ∨ True) ∧ (p5 ∧ ((p3 → p5) → p4)))) ∨ True)))) ∨ True))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230272992962709126628483161974 : (((False ∨ p3) ∧ p5) → ((p2 ∧ True) ∨ ((p4 ∨ (p4 ∨ (p2 ∧ (((p3 → p3) ∨ p2) → (p5 → p5))))) → (((p2 ∨ p3) ∧ p1) ∨ p5)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143834920048750603510545485512 : (((((((False ∧ p5) ∨ False) ∧ (p2 ∧ p1)) → (p5 → (p5 ∨ (p1 → (p5 ∧ (p4 ∨ False)))))) → p4) ∨ True) ∧ ((p4 ∨ p3) → (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48457570026887946057653414545 : (((((((True → (((p5 ∨ p4) → ((True ∧ p5) ∨ (p2 ∨ (p3 ∨ p1)))) → p1)) ∧ p2) ∨ p5) ∨ p5) ∧ p4) ∧ (False ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207539987278847144346837109016 : ((((True → (p1 → p2)) ∧ p2) → p2) → (p1 ∨ (p2 → ((p1 → ((p5 ∨ ((p4 ∨ p4) ∨ p4)) ∨ (p5 ∧ p1))) ∨ ((p3 ∧ p4) → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134405957020502554176161919869 : (((p1 → (((p1 ∨ ((((p3 ∨ (p3 ∧ (True ∨ p1))) ∧ p1) → p5) → (p5 ∧ (p1 → p1)))) → p1) → False)) ∨ False) ∨ (p5 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138324492826170827670216671648 : ((p3 → (p5 ∧ ((p2 ∧ (p1 ∨ p2)) ∨ (((((p5 ∧ False) ∧ ((p5 ∨ (False ∧ p2)) → p4)) ∨ p3) ∧ p5) ∨ p2)))) ∨ (p4 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265694343582703876739477244281 : (True ∧ (p3 ∨ ((((((p1 ∧ p3) ∨ True) ∧ p5) ∧ (((p5 ∨ True) ∨ (p2 → ((False → False) → True))) ∨ (p1 ∨ (True → p3)))) → False) ∨ True))) := by
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
theorem thm_5_vars_231264171661508050936991010165 : (((p4 ∨ p5) ∨ False) → (((p3 ∨ p1) → (p2 → (False ∧ p5))) ∨ (((p2 ∧ p4) → (p5 → (p5 ∨ p1))) ∨ (p1 ∨ (p5 ∨ (p4 ∨ p1)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172902791408334960923961099609 : ((p2 ∧ ((p4 ∧ ((False ∨ (p2 ∨ ((False → p3) ∧ (True → True)))) ∧ p4)) → False)) ∨ (p4 ∨ ((((False ∧ p5) ∨ p3) → p3) ∨ (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116832910949209316288108027276 : (((p5 ∨ p4) ∨ (p2 ∨ (((False → (False → (((True ∧ True) → p4) ∨ (((p2 ∧ True) → False) → (p3 ∨ p5))))) ∨ p2) ∧ p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181424221195686139462855716296 : ((p2 ∨ (p5 ∨ ((True ∨ (True ∧ (p1 → (True → (True ∧ False))))) ∨ p4))) → ((p3 ∨ ((p4 → True) ∧ p4)) → ((p1 → (p3 ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
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
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622469358045937421889149372799 : ((((p3 ∧ (p1 ∧ (((p5 → p1) ∨ p4) ∧ (((((True ∧ p2) ∨ (p4 → (p1 ∧ False))) ∧ ((p4 ∨ p2) ∨ False)) ∧ p4) ∨ True)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_678575179587827038725631859394 : (((((p2 ∧ (p2 → p3)) → ((((p3 → (p3 ∧ ((p4 ∧ p2) ∨ p1))) ∨ p3) ∧ (p1 → p4)) ∧ p3)) ∨ (((True ∧ p2) ∧ True) → p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44734038346817106912228421293 : (((((p1 → (p2 ∨ True)) → True) ∨ (((((((p2 ∧ p3) ∨ p4) ∧ p4) ∨ p2) ∨ (p1 ∧ p4)) ∨ p2) → ((True ∨ p1) ∨ p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158334890663666069975277817134 : (((p1 ∧ p1) ∧ (((p5 ∧ (p5 ∨ ((p2 ∧ ((True ∨ p5) ∨ (p5 ∨ False))) ∨ p5))) → False) → p1)) ∨ (True → ((p4 ∨ p2) → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603501142346739406594429266130 : ((((p3 ∨ ((((((False → p4) ∧ p2) → False) ∧ p1) ∨ False) ∧ ((p1 → (p3 ∧ ((p4 ∨ p5) → p3))) ∧ (True ∨ (p1 ∨ p5))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186974007808794626561210516884 : (((True ∨ (p3 ∨ p3)) ∨ ((False → ((p5 ∧ False) ∧ True)) ∨ p5)) → ((p1 ∨ (p3 ∨ p5)) ∨ (p5 → (p4 → ((True → p4) ∧ (False → p2)))))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727518464086890996471344913856 : ((((p4 ∧ (True ∨ p3)) ∨ (p4 ∨ (((p4 ∧ p2) ∨ ((p4 → p3) → False)) → (((True ∧ p5) ∨ False) ∨ (((p1 → p2) ∨ p1) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655673103779506860059050415195 : ((((((((p2 ∧ (((p1 ∨ p2) ∨ p1) → p5)) ∨ p2) ∧ (True ∨ p5)) ∧ (p3 ∨ (False ∨ p1))) ∧ ((p5 ∧ p1) ∨ p5)) ∨ (False → p4)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_350125527740120290245143745556 : (p4 → (((((((p5 ∧ (p2 ∧ p1)) ∧ (p2 ∧ True)) → False) ∧ (False → (p2 ∨ p1))) ∨ True) → (((p1 ∨ p2) ∨ p5) ∧ (p4 ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686152111308760405504928738614 : ((((((True ∨ (p3 ∨ p2)) ∨ (((p1 ∨ True) → p2) ∨ (False ∨ False))) → ((p4 ∧ p3) ∧ p4)) → ((p4 → False) ∨ (True → (p4 ∨ p5)))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∨ (p3 ∨ p2)) ∨ (((p1 ∨ True) → p2) ∨ (False ∨ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64433195374711100332167272619 : ((p1 ∨ ((False ∨ ((((p3 ∧ True) ∧ (((p3 → (p5 → True)) ∧ True) ∧ False)) ∧ (p1 → True)) ∨ (True ∧ (p5 → p1)))) ∧ (p1 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714514844002507502313868794642 : (((((p5 ∨ True) ∧ (True → (False ∨ False))) → (((((((False → p4) ∧ p3) → False) → (False ∧ True)) ∧ p1) ∨ ((p5 ∨ p4) ∧ p1)) ∧ p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h19 := h15 h18
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198657975768731686374160531973 : ((p3 ∨ (p4 ∨ (p3 ∧ (True ∧ (p1 ∧ p2))))) ∨ (True → (((p2 ∧ p4) ∧ (p2 ∨ p3)) → (False → (((p1 → (p4 ∨ p3)) ∧ p4) ∨ False))))) := by
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
theorem thm_5_vars_175906626668897915343120420503 : ((((p2 ∨ p1) ∧ ((False ∧ p1) → ((True → p4) ∧ (True ∨ False)))) ∨ True) ∧ ((p2 → ((p4 ∧ ((p3 ∧ p3) ∧ False)) ∨ (p4 → p5))) ∨ True)) := by
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
theorem thm_5_vars_233771196410012628249713915007 : ((p3 ∨ (p3 ∨ True)) → ((((p2 → ((((p1 ∨ False) → p5) ∧ p5) → (True ∧ False))) → p1) ∨ p3) ∨ (p5 → (p4 → ((p2 → True) → True))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245499009352094047869962882197 : ((p2 ∧ p5) ∨ ((p4 → p5) ∨ (((p5 → (p3 ∨ True)) → p4) → ((((True → (p1 → ((True → p5) → (p2 ∧ p5)))) → p1) ∨ p3) ∨ True)))) := by
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
theorem thm_5_vars_768279131779697197987384550619 : (((p5 ∧ ((p5 → (((False → (((p4 ∨ (True ∨ p5)) ∧ p5) → p2)) ∨ ((False → p2) ∧ (p4 ∧ p3))) → p4)) ∧ (p5 → (True ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302862702972008702133478356902 : (False ∨ (True → (((((False ∧ p5) → p4) ∧ (p2 ∧ p5)) → ((False ∧ ((True ∨ True) ∧ (p1 ∧ (False ∧ p2)))) ∧ ((True → p2) ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172063999358155170477074886268 : (((((False ∨ (((p2 ∨ p4) ∨ p5) ∨ p5)) → (True ∧ p2)) → p1) → (p4 ∧ p1)) ∨ ((True ∨ p4) ∨ (p2 ∧ ((True → (p5 ∨ False)) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57942032555963660887624057412 : (((False → (False → False)) → ((p5 ∧ ((p4 → (True ∨ ((((True ∨ p5) ∧ False) ∧ p5) → (p3 → ((False ∧ p1) → p5))))) ∨ p3)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176926020180727151805445113559 : (((p5 ∨ p5) ∨ (((p4 → True) → (p4 ∨ True)) ∨ ((p2 ∧ p4) ∨ p2))) ∧ (p3 → (((((p5 → p1) → True) ∨ p5) → False) ∨ (p3 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722844140992788292677566198062 : (((((p1 ∧ p1) ∨ p1) ∧ (((True → (True ∨ ((p2 ∧ (p3 ∨ ((True ∨ True) ∨ p4))) ∨ p1))) ∨ p2) → (True → (p2 ∨ (False ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_961673801434613166520605725398 : ((((p3 ∨ p2) ∧ (p3 ∧ (((False → ((p5 ∨ (p5 ∧ p3)) → p2)) → p5) ∧ ((p5 → p2) ∧ (((False ∧ (p5 ∨ p5)) ∨ p1) → p5))))) → p2) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : (False → ((p5 ∨ (p5 ∧ p3)) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h12
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h18 := h7 h11
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h19 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h20 := h9 h19
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611631792769709739206371542875 : (((((p2 ∨ ((True ∨ ((p4 ∧ p4) → ((False ∧ p1) ∧ p2))) ∨ (p1 → ((False ∨ ((True ∧ p3) → (False ∨ True))) ∨ p2)))) → p4) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305188428358209689639649123233 : (p1 ∨ ((p1 ∧ ((p3 ∧ ((((p1 ∧ (((p1 → p3) ∧ p5) ∧ (p4 ∧ False))) → p4) ∧ p1) → False)) ∧ p5)) ∨ (((p4 → False) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61872633864868047773934975152 : ((p2 ∧ ((p4 → ((p5 ∨ ((True → True) ∨ (p2 ∧ p3))) ∨ (p4 ∧ ((p2 ∧ (True ∧ p3)) ∨ (True → (p3 → (p3 → p1))))))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192950420705105976888027672699 : ((((True ∧ False) → (p1 → (p2 ∧ p3))) ∨ (p3 ∧ p3)) → (p4 → (p1 → (((p4 ∨ p5) → (False → False)) → ((p5 → (p2 ∧ p5)) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56542748846208887328553611565 : (((p1 ∨ (p4 → (False ∨ p3))) → (p4 ∨ ((((p2 ∨ p3) ∨ (p5 ∨ (p2 ∨ (p3 ∧ (p3 ∧ (p5 ∧ True)))))) ∨ p1) ∨ (False ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247540714804025069660149787937 : ((False ∨ p4) ∨ (((False ∧ (True ∧ ((p5 ∧ (p3 ∨ False)) ∨ (False ∧ (True → (p3 → p3)))))) ∧ (p1 → ((p1 ∧ p1) ∧ True))) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717773234889174707518590706272 : ((((((p1 ∧ p2) → p3) ∧ True) ∨ ((True ∧ True) → ((((p2 ∧ ((False ∨ False) ∧ p2)) ∨ True) ∧ (p2 ∨ (p5 ∧ (p3 → p1)))) ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122053005758534546297284078906 : (((p1 → ((True → ((((p3 ∨ (p2 ∨ True)) ∧ p1) ∧ True) ∧ (p2 ∧ False))) → (p1 → (False ∧ (p5 ∧ (p1 ∧ p2)))))) → False) → (p2 ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((True → ((((p3 ∨ (p2 ∨ True)) ∧ p1) ∧ True) ∧ (p2 ∧ False))) → (p1 → (False ∧ (p5 ∧ (p1 ∧ p2)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h2
  -- False on the left can always be used.
  apply False.elim h18
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : (p1 → ((True → ((((p3 ∨ (p2 ∨ True)) ∧ p1) ∧ True) ∧ (p2 ∧ False))) → (p1 → (False ∧ (p5 ∧ (p1 ∧ p2)))))) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Implications on the right can always be decomposed.
    intro h22
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h24 := h21 h23
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- False on the left can always be used.
    apply False.elim h26
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h27 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h28 := h21 h27
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- False on the left can always be used.
    apply False.elim h30
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h20
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h31 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h32 := h21 h31
    -- We need to get the right conjuct of h32 based on <expert-advice>.
    let h33 := h32.right
    -- We need to get the right conjuct of h33 based on <expert-advice>.
    let h34 := h33.right
    -- False on the left can always be used.
    apply False.elim h34
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h35 := h1 h19
  -- False on the left can always be used.
  apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54357615696747690762764333249 : (((p3 ∨ (p4 ∧ ((p3 ∨ (p2 → True)) ∨ p3))) ∧ (p1 → ((p3 ∧ ((p4 ∨ ((p4 ∧ p2) ∧ (p4 ∧ True))) ∧ (True ∧ p3))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306410135798092277507133867731 : (p1 ∨ ((p2 ∧ p2) ∨ (((False ∨ ((p4 → p1) ∨ (((p1 ∧ p5) → (p4 ∨ (((True → p3) ∨ p5) → False))) ∧ p2))) ∨ p1) ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786421318984578889827199580267 : (((p4 ∨ (((p1 ∧ ((((p2 ∨ True) → (True ∧ p1)) ∧ p4) ∧ p5)) → (False ∧ p2)) ∨ (((p1 ∨ ((p3 ∧ False) ∧ p4)) ∧ p5) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309658161632255226219536803085 : (p2 ∨ ((True → (((p2 ∧ p2) ∧ (p3 → (True ∧ (p5 ∨ p4)))) → (False ∨ ((p5 → ((True ∧ p1) ∧ p3)) ∨ p4)))) ∨ ((p2 ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177970217565511869119790128081 : ((((p3 → True) → (p5 ∨ (p4 → (p2 ∧ (True → (p1 ∧ p2)))))) ∨ True) ∨ (p3 ∧ (((((p1 → p3) ∨ p3) → p1) → p3) ∨ (p1 ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113198743803186598337390756979 : ((((((True ∧ True) ∧ (((((((p4 ∨ (p1 ∨ False)) ∧ False) ∧ p3) ∨ p3) ∧ p4) ∨ p3) ∧ p2)) ∧ True) ∨ p3) ∧ (p5 ∧ p1)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60289352127114579739663384677 : (((p1 → False) → (((((p1 ∧ (True → ((p5 → p2) ∧ p4))) ∨ p3) ∨ (True ∨ ((p3 ∧ (p4 → (True → p1))) ∨ p1))) ∧ p4) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_874357517567995365997906789766 : ((((((((((True ∨ p2) ∧ ((p1 ∨ p2) ∨ ((p2 ∧ (p5 → p3)) ∧ p4))) ∧ p2) ∨ (p1 ∧ p2)) ∧ p5) ∨ p4) ∧ p3) ∧ (True → False)) → False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h17 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h18 := h3 h17
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h20 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h21 := h3 h20
            -- False on the left can always be used.
            apply False.elim h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Conjunctions on the left can always be decomposed.
          let h25 := h23.left
          let h26 := h23.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h28 := h3 h27
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h32 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h33 := h3 h32
            -- False on the left can always be used.
            apply False.elim h33
          case inr h34 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h35 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h36 := h3 h35
            -- False on the left can always be used.
            apply False.elim h36
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- Conjunctions on the left can always be decomposed.
          let h40 := h38.left
          let h41 := h38.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h42 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h43 := h3 h42
          -- False on the left can always be used.
          apply False.elim h43
    case inr h44 =>
      -- Conjunctions on the left can always be decomposed.
      let h45 := h44.left
      let h46 := h44.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h47 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h48 := h3 h47
      -- False on the left can always be used.
      apply False.elim h48
  case inr h49 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h50 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h51 := h3 h50
    -- False on the left can always be used.
    apply False.elim h51
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350243310189647955012527155475 : (p4 → ((True ∧ (((p2 → ((p2 ∨ (p2 ∧ False)) ∧ False)) ∨ (p3 ∧ (p3 → (p4 ∧ (((p1 ∨ p4) → False) ∧ p2))))) ∧ (False → p4))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719973601297009008285733590207 : ((((((True ∨ p4) ∧ p2) ∧ p5) → ((((p3 → p3) ∨ (p3 ∨ (((p2 ∨ p5) → ((p3 ∨ p3) → p1)) ∧ p5))) ∨ True) → (p1 ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      let h5 := h1.left
      let h6 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h22.left
        let h25 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h34 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351472310422515592535936373170 : (p4 → ((p4 ∨ (((p3 → True) ∨ p1) ∨ (((p5 → (True ∨ ((p1 ∧ True) → p4))) → (p5 ∧ p5)) → p2))) → (p5 ∨ ((p5 ∨ p4) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178605629449623089480468287038 : (((p3 ∧ ((p3 ∧ p3) ∧ (p2 ∧ p1))) ∨ (p5 ∧ (False ∨ (False ∧ p1)))) ∨ ((False ∧ p4) → ((((p4 ∨ False) ∧ (p3 → False)) ∨ p4) ∧ p4))) := by
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
theorem thm_5_vars_648020897052488839968377185029 : ((((((p4 → (((p4 ∨ p4) ∧ (True ∧ p2)) ∨ ((True ∧ p3) ∨ False))) ∧ (((p2 ∨ p3) ∧ False) ∨ (p3 ∨ False))) ∧ p3) ∧ (p3 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49747209566602550867759844502 : (((p4 ∧ (p1 ∨ (((((((p2 ∧ True) ∧ ((p4 ∧ p1) ∧ p2)) ∨ p1) → p2) → (p4 ∨ p5)) → p4) ∧ True))) → ((p5 ∨ p3) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54005459314040729419331604715 : (((((p5 ∨ ((p4 ∨ (p3 → False)) → p2)) → p3) → p5) → (((p3 → ((p4 ∧ (p3 ∧ (p4 ∧ p3))) ∨ p2)) ∨ p2) ∧ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248409866501447798493923417339 : ((p2 ∨ p4) ∨ ((p3 ∨ (p2 ∧ p2)) ∨ (p4 → (((p3 → True) ∨ p3) ∧ (((p1 ∨ False) ∧ (True ∨ False)) → ((p4 → (p4 ∨ p1)) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317825688666345181230691728414 : (p4 ∨ ((((p4 ∧ (p1 → p1)) → p4) → ((((p2 → (p4 ∨ p1)) ∧ False) ∧ (False ∧ (p4 ∧ p5))) ∨ ((p3 ∧ p2) → (p4 ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244032894389176218685966842924 : ((True ∧ p2) ∨ ((((p1 ∧ (False → p2)) ∨ p1) ∨ p2) ∨ (p2 ∨ (True ∨ (p1 ∧ (p2 ∧ (p2 ∨ (p3 → (((p2 ∧ p3) ∧ p3) ∧ p2))))))))) := by
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
theorem thm_5_vars_244225076260600172260825971564 : ((True ∧ p5) ∨ ((p2 → p2) → (((((p1 ∨ True) ∨ False) ∨ ((p2 ∧ p2) ∨ p4)) → ((False ∨ p3) ∨ (p4 → p3))) ∨ (p5 ∨ (True → True))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128532663813309280751494587802 : ((p5 → (p1 ∨ (p1 ∧ ((((p1 → p2) → p2) ∨ p1) ∧ ((False ∨ p1) ∨ ((((True → True) ∨ (True → p4)) ∨ p2) ∨ p1)))))) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49681234023038622673009271693 : ((((p5 ∨ True) ∧ ((False → (p4 ∧ p5)) ∧ (((((p4 → p3) ∧ p5) ∨ (False ∧ p3)) → p1) ∨ (p4 ∨ p5)))) → (p1 ∧ (False ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164498171570813668479404056972 : (((((p2 → (True ∧ False)) ∨ (p4 ∧ (((True ∨ p2) → (p1 ∧ p1)) ∨ False))) → p5) ∧ p4) ∨ (p4 → (((p4 ∨ p2) → p4) ∨ (True → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792888196440016141187615769597 : (((True → ((False ∨ (True ∧ p1)) → ((((p3 ∨ (True ∧ (False → p1))) ∧ ((p4 ∧ (p3 ∧ False)) ∨ False)) ∧ p3) ∨ ((True → p3) → p1)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356571617406468105664334671805 : (p5 → ((p5 ∧ (p5 → ((((p4 → True) ∨ p1) ∧ p1) ∧ False))) → (p1 ∧ ((((p4 ∧ (p5 → (p3 ∨ p4))) → p3) ∨ (p1 ∨ p4)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h16 := h14 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336136332358115925465270685489 : (p1 → (((p4 ∧ (p4 → ((((False ∨ (p1 ∨ p4)) ∧ (p2 ∨ (False ∨ (p3 ∨ p3)))) ∧ (p4 ∧ p2)) → (True → (p5 ∧ False))))) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171739974893593024889824306574 : (((((((False → ((p3 ∧ p1) → True)) ∨ p5) → p1) ∧ (p4 → True)) ∨ p2) → p1) ∨ ((((p4 → (False ∨ (p1 → p4))) ∨ p5) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (False ∨ (p1 → p4))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111025362001641502717831872657 : (((((p2 ∨ (p5 → True)) → ((((p2 → (p5 ∧ ((p5 ∧ p4) ∧ p2))) → p4) ∧ p1) ∧ False)) → (p1 ∧ (p3 ∨ p3))) ∧ p2) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42659722358331350436038761229 : (((p4 ∨ ((((p5 ∨ (p4 → p2)) ∧ (p3 ∨ (p2 ∧ p5))) → (((p1 ∨ True) → p1) ∧ p4)) ∨ ((p2 ∧ (p5 ∨ p2)) ∨ True))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346395586229983111905814217506 : (p3 → ((p4 → (((p1 ∧ (p3 → (p1 ∨ ((p5 ∨ p5) ∨ False)))) ∨ p2) ∨ (True ∧ (p5 → (p4 ∨ ((p4 ∨ p2) → False)))))) ∨ (False ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22158949755207545811131537090 : ((((p3 ∨ False) ∧ ((False ∨ p3) ∨ (p2 ∧ p4))) ∨ ((True ∨ False) ∨ ((True → ((True ∧ (p4 ∨ p5)) → (p3 → (p4 ∧ p3)))) → False))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_733021688403423346968977118602 : ((((p2 ∧ p4) ∧ (p1 ∨ (True ∧ (((True ∧ (p5 → p5)) ∨ True) ∧ (((p1 ∨ p3) → (((p2 ∨ p4) ∧ p4) ∨ p1)) → (p5 ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169880061457285117609889056137 : ((((p4 ∧ (p2 → p3)) → ((p3 → ((p1 ∧ p1) ∧ p1)) ∧ p1)) ∨ (False → p4)) ∧ (True ∧ (((True ∧ ((p1 → p2) ∧ p4)) ∨ True) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
theorem thm_5_vars_49114343421811297121232601520 : (((((p5 ∨ p4) ∧ ((True → (((p3 → p5) ∨ p2) ∨ (p3 ∨ True))) ∨ True)) ∨ ((p1 ∧ p4) ∧ (p1 ∨ p4))) ∨ ((p2 ∨ False) → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190739083445454803592310937548 : (((p1 ∧ ((p3 ∧ p3) ∧ (True ∨ p5))) ∧ (p5 ∧ p5)) ∨ ((((False ∧ p2) → ((p3 → True) ∧ (p5 ∧ ((False → p2) → p1)))) → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200119404137417010347723593332 : (((p1 ∨ (p5 ∨ False)) ∧ (p1 → (p5 ∧ p4))) → (((p1 ∨ ((p4 ∧ p2) → ((p4 ∨ True) ∧ (((False ∨ p2) → p3) ∧ False)))) → p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148333816515908869385966476358 : (((((((p5 → True) ∧ ((p1 → False) ∨ p3)) ∨ p3) ∧ (False → p2)) → p2) ∧ (p5 → (p5 ∨ (p5 ∧ False)))) ∨ ((True ∧ (False ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10571984906555199317692231877 : (((p4 → ((p5 ∧ (((p3 → ((p2 → ((p5 ∧ (p1 ∧ (p3 ∧ p4))) → True)) ∨ p3)) ∨ p3) → False)) ∧ ((p2 → p2) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597403153945274944992115344247 : ((((((p2 ∧ (p3 ∨ True)) ∨ p2) ∨ (((True → (((p5 → (p3 ∨ p4)) ∧ (((False ∨ p3) ∨ p1) → p2)) ∨ True)) ∨ p4) ∨ p1)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



