variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112445855841143291824573287548 : ((((((True → p1) → ((p1 → ((p1 ∧ (p4 → p2)) ∧ (p5 ∧ ((p1 ∨ p1) ∧ p2)))) ∨ (p5 ∨ True))) → True) ∨ p3) → p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69052106565028884679986531116 : ((p5 → ((p3 ∧ ((p1 ∨ (p2 → ((p5 ∨ ((p1 → p3) ∨ p3)) → (p4 → ((p2 → p5) ∨ (p2 → p4)))))) ∧ (p2 ∧ p5))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160855738126094074524005749237 : ((((p2 ∧ True) ∨ (False ∨ p1)) ∧ (p2 → ((p4 → (((True ∨ (False → True)) → p4) ∧ p3)) → p5))) → ((p3 ∨ p1) ∨ (p4 → (p4 → p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678118914919722624232413085613 : (((((True ∧ (p5 ∨ ((p2 ∧ (False ∧ p2)) ∨ ((p5 ∨ p1) → p2)))) ∧ (p5 ∨ ((False → p4) ∨ p4))) ∨ ((p1 → (p2 ∧ True)) → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_171564664997281611498413430322 : ((((p3 → (p4 ∨ ((((p3 ∨ (p1 ∨ p3)) → p3) ∨ p4) ∨ p1))) → False) ∨ True) ∨ (False ∧ ((False ∨ ((False ∧ p3) ∧ (p2 ∨ p5))) ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774841169250649736773562273634 : (((False ∨ (((p1 → p5) → (False ∧ p1)) ∧ (((p2 ∨ ((p4 → True) ∨ p4)) ∧ ((p3 → p4) → (True → True))) ∧ ((p5 ∧ p4) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184900524183773241127056164348 : ((((p4 ∨ p5) ∧ p1) ∨ ((p4 → ((p3 ∨ p3) ∨ False)) ∨ True)) ∨ (((p2 → (p3 ∧ p5)) → ((((p4 ∧ p2) ∨ p1) ∨ p2) → False)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344591732649142932316413755410 : (p2 → (p1 → (((p5 ∨ ((False ∧ p3) ∨ p3)) ∨ (((False ∧ (((((p1 ∨ p3) → p3) ∨ p1) ∨ p4) → True)) ∨ (p5 ∨ p2)) ∧ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161310278609293747808868691061 : ((True ∧ (((True ∨ (p3 ∧ p3)) ∨ (p3 → ((p1 ∧ p4) ∧ ((p2 → p2) → (p5 ∧ p5))))) → p1)) → (p3 ∨ (((p1 ∨ p4) ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49609464609118706894055466971 : ((((False ∨ (True → ((p1 → p4) ∧ (True ∧ (p2 ∨ p4))))) → (p5 ∨ ((p4 ∧ (True ∧ (True ∧ p2))) → p3))) → ((p4 → False) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733202515692827392468720651852 : ((((p3 ∧ p2) ∧ ((p1 ∧ ((p5 ∧ (p2 → ((True ∧ ((False → True) ∧ p1)) ∧ p3))) ∨ p2)) ∧ ((p3 ∧ (True → p4)) ∨ (p4 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173476408685831438345434184305 : ((((p5 → ((True → (p3 ∧ (False ∨ True))) → ((False ∧ p1) → p2))) ∨ p3) ∧ p5) → (p2 → (((p3 ∨ True) ∨ (p5 ∨ True)) ∧ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117157100910303932467189654772 : ((True ∧ ((((p1 ∧ p4) ∨ (True → ((((((True ∨ ((p5 ∨ p3) ∨ p5)) ∧ p3) ∧ p4) ∧ p3) ∨ False) → p1))) → p5) ∨ False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53069088886147016322540046433 : (((p1 ∧ ((p4 ∨ p2) ∨ (p4 ∨ ((p4 ∧ p5) → (p4 ∧ p5))))) ∧ (((p5 ∨ p5) ∨ p1) ∧ (((False → p2) ∧ (p1 ∧ p3)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256989135329630905226233994366 : ((p1 ∨ p5) → (p5 ∨ ((((p5 → p5) ∧ (p3 ∧ True)) → (((((p4 ∨ p4) ∨ p4) → p2) ∧ (True ∧ (p2 ∨ (p3 ∨ True)))) → p4)) ∨ True))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607944122167167640966813717197 : (((((p2 → ((((p4 → True) ∨ ((p4 ∨ (((p4 ∨ p5) → p3) ∨ (p5 ∧ p1))) ∧ (p4 ∧ (p4 ∨ p3)))) → p4) ∨ False)) ∧ p4) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175352146900278507816313266777 : ((p5 ∨ ((p4 ∧ (p4 ∧ (p4 ∨ p4))) ∧ ((True ∧ p2) ∨ ((p2 ∧ p5) ∧ True)))) → (p2 → (p5 ∨ ((p1 ∧ p4) ∨ (p1 ∨ (p5 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h29 := h27.left
        let h30 := h27.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158373224168102498724552030280 : (((p4 ∨ p5) ∧ ((p5 ∧ True) ∧ (((p4 → (p2 ∧ p2)) ∨ False) ∨ (True → ((False ∨ True) ∧ False))))) ∨ ((False → ((p3 ∨ p4) → p4)) ∨ p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39889656093817103891719074834 : (((p2 → ((p3 ∧ True) ∧ (((p2 ∧ (p5 → (p2 ∧ (p1 ∧ True)))) ∧ True) → ((p1 ∨ p1) ∨ (p1 ∨ ((False ∨ p2) → p1)))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165783125962397812402574858862 : (((p3 ∧ ((p5 ∧ True) → True)) → ((((p4 → p1) → (False ∨ (p2 ∧ p2))) ∧ p3) → p5)) ∨ (p5 ∨ (((p3 ∨ (p3 ∨ p3)) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_38249016987019664624195603157 : ((((((p1 ∨ ((p4 → (p3 ∧ p3)) ∨ p5)) ∨ (p1 ∨ False)) → (((p5 ∨ False) → p4) ∨ p2)) ∧ ((True ∧ (p4 ∨ True)) ∨ False)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148817287299565141527289043734 : ((((p2 → p2) → ((False → p3) → True)) → (p3 → ((((p4 ∧ (p5 ∧ True)) ∧ (p2 ∧ True)) ∨ p2) ∧ False))) ∨ (((p4 → p1) ∧ p2) → p2)) := by
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
theorem thm_5_vars_137051150180081042585170501300 : (((p1 → False) → (((p5 ∨ False) ∨ p5) ∨ ((p5 ∨ (((p2 → p2) ∨ (False → p2)) → p4)) ∨ ((p2 → p3) → p5)))) ∨ ((p4 → p4) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615943377652005588339761705217 : (((((((p1 ∨ p1) ∨ (((p1 ∧ True) ∧ p2) → (True ∧ (True ∨ p2)))) ∧ p4) → (((p4 → (p1 ∧ False)) ∨ (p3 → p4)) ∨ p4)) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726269184148834666713665928944 : (((((p1 ∨ p2) ∨ p3) ∨ ((((False ∨ (p1 ∨ p1)) ∨ (p4 ∨ True)) ∧ True) ∨ (True → (False ∧ (((False → p3) → False) ∨ (p3 ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197243577371711812812665015476 : (((((p5 ∧ p1) ∧ (p2 ∨ False)) → p4) → p5) ∨ ((True → (False ∧ False)) → ((True ∨ (True ∧ ((((p1 ∧ p4) ∨ True) → p5) ∨ p4))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205540000404848488317603229032 : (((p2 ∨ p1) ∧ (False → (p4 ∨ False))) ∨ (((p4 ∧ False) ∨ p5) ∨ (p5 → (False → (False ∧ (p2 ∨ (False ∨ ((p1 ∧ p4) → (False ∨ p5))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49168875415045998036942093096 : ((((((p4 ∨ p4) → (p4 ∨ p1)) ∧ p5) → (True ∧ ((False → (p3 → p5)) ∧ (p1 ∧ (False ∨ (True ∨ p5)))))) ∨ (p3 ∨ (True ∧ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226055535747322827442869944505 : (((p5 ∧ p2) ∨ p5) ∨ (((p5 ∨ (p1 ∧ p4)) → ((False ∧ p1) ∨ False)) ∨ ((True ∧ (((True ∧ p2) → (p2 ∨ (p2 → p1))) ∧ p1)) → p1))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125980431673390450715290254700 : (((p4 ∨ p4) → (p1 ∧ (((((True ∧ p5) → (((p4 → p1) → (p3 ∧ p5)) → (p4 ∧ p2))) → p5) → (False ∧ p1)) ∧ p4))) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748669838339333877872184747706 : ((((p3 → p3) → (((((((p5 → p1) ∧ p4) → p2) ∨ (True → p3)) → p2) ∨ (((p2 ∨ False) → p2) → p4)) → ((p4 ∧ p1) ∨ True))) ∨ p4) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119563529312616073051040103653 : ((p5 → ((False → (((True ∨ p3) ∧ p5) → (p1 ∨ (False ∨ p2)))) ∧ ((((p1 ∧ True) ∨ p5) → (True ∧ (p3 → True))) → p1))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_961313871461681305189928352403 : ((((p2 ∨ False) ∧ ((True ∨ (p2 ∧ p1)) → (((p3 → (p2 → (((p1 ∧ (p1 ∨ p3)) ∧ p4) → p2))) ∧ ((p5 ∧ False) ∨ p4)) ∧ p3))) → p4) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (p2 ∧ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64199535979418402304928246221 : ((False ∨ (p1 ∧ ((p4 ∧ ((p4 ∧ p2) ∧ (((p1 ∨ p3) ∨ ((p5 ∨ False) → (False ∧ (p3 ∨ p2)))) ∧ ((p2 ∧ p2) ∨ False)))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774834367840942952715569664435 : (((False ∨ (((p3 ∨ (False ∧ p4)) → True) ∧ ((((((p4 ∨ p4) ∨ (p3 ∧ ((p1 → True) → p1))) ∨ p3) ∨ p4) ∧ (False ∧ p3)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654814450666889304037565809168 : ((((((((((True ∨ p2) ∧ p1) → (p1 → p4)) → ((True → False) ∧ (p1 ∧ True))) → (False ∨ p1)) ∨ (p4 → False)) → False) ∨ (False → p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_1133680257263776941675560221 : (((((((False ∧ False) ∨ p3) → False) ∧ p3) ∨ p1) ∧ ((False → ((p5 ∨ False) ∧ ((p3 ∧ ((True ∧ False) → p3)) ∨ False))) ∧ p3)) → p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : ((False ∧ False) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302752270137430776762119116508 : (False ∨ (p4 ∨ ((p1 ∨ (True → (p4 ∧ (((p2 ∨ p2) ∨ (p2 ∨ p4)) → ((p5 ∨ (False ∧ p1)) → ((p3 → False) → p2)))))) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_204396935459387402536507627746 : (((False → (p2 → (p1 ∨ p5))) ∧ p4) ∨ ((p2 ∧ (p2 ∨ False)) ∨ (p1 ∨ (((p1 → p1) → (p2 ∧ (p2 ∨ (True ∧ p2)))) → (p2 → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55624918558470822058962319560 : (((p4 → (p1 ∨ ((p5 → p2) ∧ p2))) → (p5 → (((((p1 ∨ p4) → (p2 ∨ p2)) → p1) ∨ (p5 ∨ (p2 → (p5 → p5)))) ∨ False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314456546368608752754512490421 : (p3 ∨ (((((False → (False ∨ (p1 → p1))) ∨ (p1 → (((True → p3) → p2) ∧ (p3 ∨ True)))) → p3) → True) → (((False → True) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174155486489953814114295117882 : ((((False ∧ ((p3 ∧ False) ∧ (p2 ∨ p1))) ∨ (p3 ∨ (p2 ∨ p5))) ∨ (p4 ∧ False)) → ((p2 ∨ p4) → (((p4 ∧ False) ∧ p2) ∨ (p5 → True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- False on the left can always be used.
        apply False.elim h6
      case inr h8 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h29
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h30 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h31
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- False on the left can always be used.
      apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175404239429458310687211973240 : ((False → ((((True ∧ (p3 → p2)) → p3) ∧ (True ∨ (True → (p3 ∨ p1)))) → False)) → (((p4 ∧ (False → True)) ∨ p4) → ((p2 ∧ p5) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147343949386896817077412452051 : ((((((((p2 ∧ p3) → p1) ∧ True) ∧ True) → ((p5 → p5) ∨ ((p2 ∧ False) → True))) → (False ∧ p5)) ∨ True) ∨ ((True ∧ (p5 ∧ p4)) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166416193742919802848592187426 : ((p1 ∨ ((True → (((False → True) ∨ ((True → p2) ∧ p2)) ∨ (p5 → p3))) ∧ (True → False))) ∨ (((p2 ∨ (True → p2)) → p5) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311205978326777292495673386037 : (p2 ∨ ((p5 ∨ False) → ((((p3 ∧ p1) → (False ∨ (((False ∨ p4) → ((False ∧ p2) ∧ False)) → False))) ∨ p4) ∨ (p5 ∧ ((p4 ∨ p5) → True))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180255180675995663321847567454 : (((p2 ∨ (((p1 → p3) ∧ p3) ∧ ((False ∨ p4) ∧ (p2 ∨ p1)))) → p2) → (((p1 ∨ (((p4 ∨ p1) ∧ p1) → (True ∧ False))) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117696500608787676640521138864 : ((p3 ∧ ((p5 ∨ p4) ∨ (False ∨ (((p1 → (True → ((p3 ∨ (p2 ∨ p2)) → ((p5 ∨ p2) → p5)))) ∨ (p4 ∧ False)) → p1)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708802057274334625019345911578 : (((((True → ((p1 ∨ p1) → (p5 ∨ False))) → True) → (p3 → (p2 ∧ ((p2 ∨ (True ∨ p2)) ∧ (False ∧ (p4 ∨ ((p4 ∨ p1) ∨ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302640686346995826614963584322 : (False ∨ (p2 ∨ ((((True ∧ ((p1 ∨ p2) ∨ False)) ∨ (p2 → p5)) ∨ (p4 → p3)) ∨ ((((p2 ∧ p5) ∨ ((p2 ∨ p1) → False)) ∧ p2) → True)))) := by
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
theorem thm_5_vars_655824489056167478576463635099 : (((((((((p1 ∧ (((p2 ∨ (p4 ∨ p3)) ∨ p3) ∧ True)) → (p3 → p2)) ∧ p5) → p1) ∨ False) → ((p3 → p5) ∨ p1)) ∨ (p1 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_133727093731114281797415936420 : ((((((p3 ∧ True) ∨ p4) ∨ ((True ∧ p1) ∧ ((False ∧ False) → p2))) → (False ∨ ((p5 ∧ p5) → (p5 ∧ False)))) ∧ p1) ∨ (False → (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711643312670170231414611010883 : ((((p3 → (False ∨ ((p2 ∨ True) ∨ False))) ∧ (((p3 ∨ p2) → p5) ∨ (p4 ∨ (True → ((((False ∧ (False ∨ p3)) ∧ p4) ∧ p1) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43250300439367354960990065514 : ((((True → (False ∨ ((((p5 ∨ (p4 → p3)) → p1) ∨ (((p4 → p2) ∧ False) ∨ False)) → (p3 ∨ ((p4 ∨ p1) → True))))) ∧ p3) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41452308725484774661387481053 : ((((((p2 → False) → ((p1 ∧ ((p5 ∨ p4) ∨ p3)) → True)) → False) ∧ ((((p1 → p4) → (p2 ∨ False)) ∨ (p3 ∧ False)) ∧ p3)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354745225415759362429460533942 : (p5 → ((((((((p5 → (False ∧ (p3 → False))) ∨ p1) ∨ (p5 ∨ p3)) → p5) ∨ p1) → p4) ∨ (p3 ∨ (True ∨ (True → (p3 ∧ False))))) ∨ False)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697754892365985072460381962366 : ((((p2 → ((p1 ∧ (((p5 ∨ p3) → p1) ∨ (p3 → p2))) → p2)) ∧ (((True → p3) ∨ (p5 ∧ (p2 → True))) → ((p5 ∨ p1) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135060762626006273529488058043 : (((((((p5 ∧ (p5 ∨ p4)) ∧ True) ∧ True) ∨ (p4 → (p3 ∨ (((p4 → p2) ∨ False) ∧ True)))) → p2) ∨ (p1 ∧ False)) ∨ ((p5 ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42614994241705112185924120077 : (((p3 ∨ ((((p5 ∨ (p3 ∨ p1)) → (((p4 ∧ p3) → ((p5 ∨ p2) ∨ p4)) ∨ (p4 ∧ (p3 ∨ True)))) ∨ p3) ∧ (False → True))) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  -- Implications on the right can always be decomposed.
  intro h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701875394747658545888064114167 : ((((True ∨ (True ∨ ((((p3 ∨ p2) ∨ False) ∧ False) ∧ p2))) ∧ (((False ∨ ((p5 ∨ True) → p2)) ∧ (False ∨ (False → True))) ∨ (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215432741352373990140983804601 : ((p3 ∧ ((p4 ∨ p2) ∨ False)) ∨ (False ∨ (p5 → ((p3 ∨ (True → (p3 ∧ (p4 ∧ p5)))) → (((p2 → p5) → True) → ((p5 ∨ False) ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329696411437208863925486024771 : (True → ((p4 ∨ p5) → (((((p5 ∨ p4) → p5) ∧ ((p5 ∨ p3) → (p5 ∧ p4))) ∧ (((p1 ∨ (p5 ∨ p5)) ∧ p1) → (False → p4))) → p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (p5 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127733110326772875195197815968 : ((True → ((p1 ∨ ((False → (p3 ∨ p2)) → (p2 → (False ∨ ((p3 ∨ p3) ∨ ((((p2 ∧ False) ∨ p1) ∨ p1) ∧ p2)))))) ∧ False)) → (p4 ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715631036109395650153342556956 : (((((True → (False ∧ p3)) ∧ p4) ∧ (False ∧ (p5 ∧ (p2 ∧ (p3 ∧ ((p2 → (True ∨ (p1 ∨ (p2 → p1)))) ∧ (p5 ∨ (False ∧ p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315687193422095777168818844346 : (p3 ∨ ((False ∨ p5) ∨ (p2 ∨ ((p2 → ((p5 ∧ ((((p3 ∧ ((p4 ∨ p1) → ((False ∨ p3) ∧ True))) ∧ p2) → p4) ∧ p3)) → p4)) ∨ True)))) := by
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
theorem thm_5_vars_186993782934743872809574318155 : ((((False → p3) ∧ True) → (p2 ∧ (p4 → (p2 ∨ (p4 ∧ True))))) → (True ∧ (p5 → (p3 → (p5 ∧ ((p2 ∧ (p3 → (p1 ∧ p4))) → p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595486338092230087059581093489 : ((((((p3 ∨ (p4 → True)) ∧ ((p2 → ((p5 → p3) ∧ False)) ∧ False)) ∨ (p3 → ((p1 ∧ ((p5 ∨ (p2 → p2)) → p1)) ∨ p5))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34132424613479546060088499719 : ((True → (((p5 ∧ ((p3 ∧ False) ∨ False)) ∨ ((False ∨ p5) ∨ (p1 ∨ ((p2 ∨ ((((False ∨ True) ∨ p1) ∨ p1) ∨ p5)) ∨ p4)))) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41089534289880117074024534991 : ((((((((p4 → False) → p4) ∨ ((p1 → (p5 ∨ (p3 ∧ True))) → (False → False))) → (p2 → False)) → p4) ∧ ((True ∧ p3) ∧ False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191851257623088656316838161950 : ((p3 ∨ (p4 ∨ (((p4 → p5) → (p3 ∧ False)) ∨ p5))) ∨ (True ∧ ((p1 → (p3 → (((p4 ∨ (p5 ∧ p4)) ∨ True) ∨ (p2 ∧ False)))) ∧ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198328983266772757592621297672 : ((p2 ∧ (((p1 ∧ p2) ∨ (True → False)) ∧ True)) ∨ ((p3 → ((p1 ∧ ((p2 ∧ (p1 → ((p3 → p5) ∧ p5))) ∧ p5)) ∨ (p5 ∨ p3))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655284044443199260604837838740 : ((((((p5 ∧ p3) ∨ (p2 ∨ (p4 → ((((True ∧ p4) ∨ ((p3 ∧ p1) ∧ p2)) ∨ p5) ∨ (p2 ∨ p3))))) ∧ (p3 → p1)) ∨ (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669468220469078495971806789307 : (((((((((p1 ∧ p2) ∧ p5) → (p1 ∨ ((p2 ∧ False) ∨ p5))) ∨ ((p1 ∧ True) ∧ p5)) ∧ p3) → (True → p2)) ∨ (False → (p5 ∨ p5))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_329033904090486137020216316782 : (True → (((p3 → p5) ∨ ((p1 ∨ p1) ∨ True)) → ((p1 → (((p5 ∨ (((p3 ∧ p1) ∨ True) ∨ (p1 ∨ p4))) ∨ p5) ∧ p1)) ∨ (p3 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
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
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
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
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58975362634200435975405606921 : (((p2 ∧ p4) ∨ ((((p1 → p2) ∧ p1) ∧ (((False ∨ ((False ∧ True) → p4)) ∧ p1) ∨ (p4 ∧ p1))) ∨ (p3 → (p3 ∨ (p5 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219158380066834096530257366357 : ((False ∨ ((p5 ∨ p1) ∧ True)) → (((p1 → p3) ∨ ((False ∨ True) ∨ (((p5 ∧ p1) ∨ (True → p3)) ∨ False))) → ((p2 ∧ p4) → (False ∨ p4)))) := by
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
    cases h1
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h28 =>
            -- False on the left can always be used.
            apply False.elim h28
          case inr h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- Disjunctions on the left can always be decomposed.
            cases h30
            case inl h32 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h33 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h35 =>
            -- False on the left can always be used.
            apply False.elim h35
          case inr h36 =>
            -- Conjunctions on the left can always be decomposed.
            let h37 := h36.left
            let h38 := h36.right
            -- Disjunctions on the left can always be decomposed.
            cases h37
            case inl h39 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h40 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
      case inr h41 =>
        -- False on the left can always be used.
        apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147344532850950333894949370537 : ((((((True → p4) → p3) ∧ (((False ∧ p1) ∧ (p1 → (p1 ∧ p1))) → (False ∨ p3))) → (p4 ∨ False)) ∨ True) ∨ (p3 ∧ (p5 ∧ (p3 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40801066088545130793670148092 : ((((False ∨ ((((True → p2) → p2) ∧ ((p1 ∨ p5) ∧ (((p2 → (p3 ∧ ((p4 ∨ p3) ∨ p1))) ∧ p3) ∨ p5))) ∨ False)) → p2) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357413291292838585426460150654 : (p5 → ((p1 ∨ True) → ((((p2 ∨ p1) → p3) ∨ p1) → ((p3 ∧ (p1 → (True → p2))) ∨ (((p2 ∧ p1) → (p3 ∨ (p2 ∨ p2))) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69277001176999278951157207436 : ((p5 → ((p3 → p4) ∨ (False ∧ (((p3 ∨ ((p2 → p1) → (True → (p2 → p1)))) ∧ (False ∨ (p1 ∨ True))) ∧ (p1 → (False ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214709828774059629351766743137 : (((p1 ∧ True) ∨ (True ∧ False)) ∨ ((((p1 ∧ ((False ∧ False) ∧ p1)) ∨ p5) ∨ (True ∨ ((p2 ∨ p5) → p3))) ∨ (((p4 → False) ∨ False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313271572126087534158502129778 : (p3 ∨ ((p1 ∧ ((False ∧ (((p3 ∧ p3) ∨ False) → True)) ∧ (p2 ∨ ((p5 ∧ (False → ((p2 ∨ True) → ((False ∨ p5) ∧ False)))) → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354031286068434444385023051569 : (p4 → (p4 → ((((((p1 ∨ ((p1 ∧ (False ∧ p4)) → ((p1 ∨ p2) ∨ p3))) ∨ p1) ∧ ((p4 ∧ p4) → p2)) ∧ p5) ∨ False) → (p2 ∨ p2)))) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h11 : (p4 ∧ p4) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h12 := h8 h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h14 : (p4 ∧ p4) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h15 := h8 h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : (p4 ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h1
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h18 := h8 h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112899899449537531072159412578 : ((((p5 → p1) ∧ (((((p3 ∧ True) ∧ (p2 ∨ p3)) ∨ p2) ∧ (((False → (p5 ∨ p1)) ∨ p1) → p5)) → (p5 ∨ False))) → p1) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52952068145009333904375376339 : ((((((p4 → True) ∧ p1) → ((p3 → (p2 → True)) → p5)) ∨ p1) ∧ (p1 ∧ ((((True ∨ p4) ∧ ((p1 ∨ p3) ∨ p3)) ∧ p3) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262185249680234080970141097215 : (True ∧ (((((True ∧ p5) ∨ (((True → (False ∧ ((((p1 ∧ False) → False) ∧ p1) → (p3 ∧ False)))) → (p1 ∨ p4)) → p1)) → False) → p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253600374527075987197402959161 : ((p1 ∧ True) → (((((p2 ∨ (p3 ∧ p2)) ∧ ((((True → False) ∧ (p5 ∧ p1)) ∨ ((True ∨ p2) → p5)) ∨ p3)) ∨ (p1 ∨ True)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252796685359197464389436353444 : ((True ∧ True) → (p2 ∨ (((p3 ∧ ((p1 → p2) → p3)) → (False ∨ p2)) → (((((True ∨ p3) ∧ p5) ∧ False) ∧ p3) ∨ ((p5 ∨ p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208527343931056206781318863137 : (((p5 ∧ p5) → (p2 ∨ (False ∧ p1))) → ((p3 ∧ p2) → ((p5 ∨ ((False ∨ (((p1 → p4) ∧ p5) → (p5 → False))) ∨ (False → p5))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323791143269776134384799629774 : (p5 ∨ ((((p3 → True) ∧ (True ∧ (((p3 ∨ (p2 ∨ True)) ∧ p2) ∧ p1))) ∧ (p3 → (False → False))) ∨ (((p1 → True) → (p4 → True)) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654568892499923722416089414196 : (((((p2 ∨ (p1 → (((p4 ∧ (p3 ∧ ((p5 ∧ False) → p3))) ∨ (((p1 → False) → (p2 ∨ p2)) → True)) ∧ p4))) ∨ p4) ∨ (p1 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213542024344572025684212726302 : ((((p2 ∧ True) ∧ p5) ∨ False) ∨ (p4 ∨ (((p2 → (((False ∧ p4) ∨ True) ∨ True)) → p3) ∨ (p2 ∨ ((p5 ∨ p1) ∨ ((p1 ∨ True) ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780103325301469470019687680264 : (((p2 ∨ ((((((p2 ∨ False) → p3) ∨ p3) ∨ p3) ∨ (p1 → ((p5 → p3) → ((p5 → False) → (True ∨ (p3 ∧ False)))))) → (p3 ∨ True))) ∨ p2) ∧ True) := by
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180623893289010856096813819204 : (((p3 ∨ (((p4 → p4) ∨ False) → True)) ∧ (((p3 ∨ p5) → p2) ∧ p2)) → ((((False → (p2 ∧ p4)) ∧ False) ∨ (p1 → p4)) ∨ (p3 → p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_886500001959132561125402993618 : ((((((((p3 ∧ p1) → p5) → (((True ∨ (p5 ∨ ((p5 ∧ (True ∨ (False ∨ p5))) ∧ True))) ∨ p3) ∧ p1)) ∨ True) ∨ p5) → (True ∧ p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∧ p1) → p5) → (((True ∨ (p5 ∨ ((p5 ∧ (True ∨ (False ∨ p5))) ∧ True))) ∨ p3) ∧ p1)) ∨ True) ∨ p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165441832007656771612393511298 : (((p4 → ((p3 ∧ ((p5 ∨ True) → (p3 ∨ (p5 → p4)))) ∧ p5)) → ((p5 ∨ False) ∨ p5)) ∨ (((p3 → (p4 ∧ p4)) ∧ (p1 ∧ p3)) → p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169101648920016778529671214724 : ((p4 → (((p4 → (False ∧ (p2 → p5))) ∨ p1) → (p4 ∨ ((p1 ∧ False) ∨ (False → False))))) → (p2 → (((p1 ∨ p4) → p4) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134305829303062744314261758413 : (((True ∧ ((((p1 → ((p2 ∨ p1) ∧ True)) → p2) ∧ ((p3 ∧ p3) → ((p2 → (p1 → False)) → False))) ∨ True)) ∨ p2) ∨ (p1 → (p3 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323777395139292820811986091044 : (p5 ∨ ((((p1 ∨ ((p1 → p2) ∨ ((p5 ∧ (p4 ∨ (p1 ∧ (p3 ∧ False)))) ∨ p3))) ∨ p3) ∧ p3) ∨ ((p1 → p1) → ((p2 ∨ p1) → True)))) := by
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
theorem thm_5_vars_244900479908587990127452446747 : ((p1 ∧ p2) ∨ (False ∨ (p2 ∨ (((p3 ∧ (False ∨ (p3 → p2))) ∨ (p4 → (p4 ∧ ((((True ∧ p1) → (p3 ∧ p3)) → False) ∧ p1)))) ∨ True)))) := by
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



