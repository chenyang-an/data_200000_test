variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305998913849617520695186633221 : (p1 ∨ (((p2 → (p2 → p1)) → p3) ∨ (p4 ∨ ((p2 → p1) → ((((p5 ∨ (p2 → False)) ∨ ((p1 ∧ p4) → p1)) ∨ (True ∨ p3)) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308443026811357048354516461983 : (p2 ∨ (((p1 → ((p4 ∨ p1) ∨ ((((((p5 ∧ True) ∨ ((p1 ∧ p3) ∧ p4)) ∨ (p1 ∨ p5)) ∧ p5) → p3) ∧ (p4 ∧ p3)))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172236024799494456195318660695 : ((((((p4 ∨ p1) → p2) ∨ (p1 ∧ p3)) → p1) ∧ (((False ∨ p5) → p5) ∨ p3)) ∨ ((((p1 ∧ p1) ∧ (p3 ∨ p4)) ∨ p2) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340989206483706758164164041897 : (p2 → (((False ∨ p5) → ((((((p1 ∧ p4) ∨ p5) → (True ∨ p4)) ∧ (p1 ∧ p5)) → (((p5 → False) → (True ∨ p4)) ∨ p5)) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206087983479736742211851929006 : ((p3 ∧ (p5 ∧ ((p2 → p1) ∧ p3))) ∨ (((p5 ∨ False) → (((p2 → p2) → ((True ∨ (False → p4)) → (False ∨ p5))) → p3)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160842004330490004249364728790 : (((((p4 → p4) → False) ∧ p4) ∧ ((((p5 ∨ p4) ∧ p3) ∧ p4) → ((p3 → (False ∨ False)) → p5))) → (p2 ∧ ((False ∧ p5) ∨ (True ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h13
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214751401743123233043536581706 : (((p4 ∧ p4) ∨ (False ∨ p3)) ∨ (p3 ∨ ((((False ∧ True) ∧ p3) ∧ (((((False ∧ p4) ∧ ((p4 ∨ p3) → p3)) → p5) ∧ True) ∧ p3)) → p3))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180239142750586522485001391412 : (((p4 ∧ ((((p1 ∧ p3) ∨ p4) ∨ ((True → p2) ∨ p5)) ∨ p2)) → p5) → ((p3 → ((False → ((True → p5) → p5)) → p5)) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149606890253121371350035123056 : ((p3 ∧ ((p2 ∨ (p5 → p4)) ∨ (((p1 ∧ p5) → True) ∧ ((p2 ∧ p2) ∧ (p5 ∨ ((True ∨ p4) ∨ p2)))))) ∨ (p2 → (p3 ∨ (p5 ∨ p2)))) := by
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
theorem thm_5_vars_690224502908203908128313542622 : ((((p5 ∨ ((p1 → (((p3 ∨ (((False → p4) ∧ p1) ∧ True)) → p5) ∧ True)) ∨ p5)) ∨ ((((p3 → (p4 → p2)) → p4) → False) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175096759173581569208813026780 : ((p3 ∧ (p5 → (p4 → (((p5 ∧ p4) → p2) ∨ (((p4 → p5) ∨ p4) ∨ p4))))) → ((False ∨ ((p1 ∧ p2) ∨ (True ∨ (p5 ∧ True)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_177974995830882785380011633490 : (((False ∧ ((p1 ∧ (p4 → ((p1 → p3) ∧ (p2 ∧ p3)))) → p5)) ∨ False) ∨ ((((p3 → ((True ∧ p3) ∨ p2)) → p5) ∨ p5) → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197714776394560160952323768910 : ((((True ∨ p4) ∧ p2) ∧ (False ∧ (p1 → p1))) ∨ (((False → (False → ((p3 ∨ True) → (p1 ∧ (p4 ∧ False))))) → ((p4 ∨ p5) ∧ False)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (False → ((p3 ∨ True) → (p1 ∧ (p4 ∧ False))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h4
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67412595637440434211001533114 : ((p1 → ((((p2 → p4) → (((p3 → p4) ∨ (((p1 ∧ p4) ∧ (True → (True ∨ p2))) ∧ (p4 ∧ p3))) ∧ p4)) ∨ p5) ∨ (p5 → p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962591344354889814072804308747 : ((((True → p5) ∧ ((p3 → (p1 ∧ (p1 ∨ (((p2 ∨ (p5 → (True ∧ (False → (False ∨ (True → (p3 ∧ p1))))))) ∧ p1) ∧ p2)))) ∧ p4)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346791954987946761947924889199 : (p3 → (((p5 → p5) ∧ ((p4 → ((p1 ∧ (False → p1)) ∧ p2)) → (p4 ∨ ((p4 ∧ p3) ∨ (p4 ∧ True))))) ∨ ((p2 → (p5 ∧ True)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791784287198515805380261396769 : (((True → ((p5 ∨ (p1 ∨ ((True ∨ (p4 ∨ p2)) ∨ ((True ∨ p2) → ((p3 ∧ ((p2 → (p1 ∨ (True ∧ p1))) ∨ p3)) → p2))))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114947021906499377284856975465 : ((((True ∨ p2) ∨ (((p1 → (((True → p1) ∧ True) ∧ False)) ∨ True) ∧ p1)) → ((p5 ∨ p4) ∧ (((p4 ∧ p1) ∨ p2) → p3))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150153772696275428653583684781 : ((p1 → (((((((p2 ∨ p1) → p4) ∧ p2) ∧ ((False ∧ p1) ∨ p3)) ∧ (False ∧ p2)) ∨ True) ∨ (p2 → p5))) ∨ (((p1 ∨ True) ∧ p5) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354035120805840567344435052113 : (p4 → (p4 → (((p4 → p3) → ((False ∨ (p5 ∧ (p5 ∧ p1))) → (((p3 → True) ∧ p3) → (p3 → (False → p4))))) → (p3 ∨ (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246587880197471877405430673433 : ((p5 ∧ p2) ∨ ((p5 ∧ (p5 ∨ p3)) ∨ ((False ∧ (p4 ∧ (p1 → p5))) → ((p2 → ((p4 ∨ (p1 ∧ p3)) ∨ p5)) → ((p5 → p5) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696938084478251454592225560179 : ((((((True ∨ (True ∨ ((p1 ∨ p1) → p4))) ∧ p4) → (False → p1)) ∧ ((True ∧ ((p2 → (p3 ∧ p3)) → (p4 ∧ p2))) ∧ (p1 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172457817154007368696850680748 : (((p2 ∧ ((False ∧ True) ∨ p1)) ∨ (((p2 ∨ (p4 ∨ (p1 → p1))) ∨ True) ∧ True)) ∨ ((p1 ∨ p4) ∧ ((p4 ∨ p4) ∧ (p5 ∨ (p2 → p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201012863103887782080330111543 : ((p3 ∨ (p4 ∨ (p2 → (False ∨ (p3 ∨ False))))) → (False ∨ ((p5 ∨ False) → (p2 ∨ (((p4 → (((p3 → p1) → p4) → p2)) → False) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219042167564954114544851528814 : ((p5 ∧ ((False ∧ p5) → True)) → (((p3 → (p5 ∧ (p4 ∧ (p1 ∧ (False ∨ (False ∧ (p4 ∨ ((p4 ∨ False) ∨ p1)))))))) ∧ p4) ∨ (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117243275394929970252474825667 : ((True ∧ (p1 ∨ (((p1 → p1) → (((p1 ∨ (True ∧ p4)) → False) → p3)) ∨ (((p1 → p4) ∨ p5) ∨ (p5 → (p1 → p1)))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804690639646995627427275746743 : (((p3 → (((p5 ∧ p2) → True) ∧ ((p3 ∧ ((p4 ∨ True) → ((p5 ∨ (((p1 ∧ p4) ∨ p4) → p2)) ∧ p4))) ∨ (True ∨ (True ∧ p1))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60614602835991802865347353239 : ((True ∧ (((p3 → (p1 ∧ ((p5 ∧ (False ∨ (False ∧ p5))) ∧ p5))) → ((p3 → ((False ∧ True) → (p2 ∨ p5))) → p1)) ∨ (p1 ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_172740049864775820584372822755 : (((p5 → p2) ∨ ((p1 → p3) → ((p2 → ((p2 ∨ True) ∧ (p3 → p5))) → p1))) ∨ (((False ∨ p5) → p5) → (True ∨ (p3 → (False ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613373583993096246996279115967 : (((((True ∧ ((True ∨ p5) ∧ ((p1 ∨ (True ∨ ((True ∧ ((p4 ∧ p2) → p2)) ∨ p1))) ∧ (p3 ∧ (p5 ∨ True))))) → (p5 → p2)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209123206185761941377770248867 : ((p2 ∨ (True → (p4 ∨ (p4 → p5)))) → (((((p2 → (p4 → p5)) ∨ (((p5 ∧ p4) → p3) ∧ p2)) ∨ (p4 ∧ False)) ∨ (True ∨ p1)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754577504801958231643153307221 : (((False ∧ (p2 ∧ (((p1 ∨ ((True → (p5 ∧ ((False ∧ (False ∧ p1)) ∧ ((False ∧ (False ∧ p1)) ∨ True)))) ∨ False)) ∧ True) ∧ (False → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626535698925917555122333986497 : ((((p4 → ((((p4 ∧ ((p1 ∧ p1) ∧ p3)) ∧ True) ∨ p1) ∧ ((p3 ∧ ((True ∨ (p2 ∧ p1)) ∧ ((p4 → p1) ∧ p4))) ∧ p4))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_49891831771563016407432541028 : ((((((p1 → p2) ∧ p4) → (((((False ∨ p3) ∧ p2) ∨ p5) ∧ p3) ∨ ((p2 ∨ True) ∨ p3))) ∨ True) ∧ (True ∨ (p4 → (p1 → True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138614168891139441942700262912 : ((((((((((p3 → True) → p3) → ((p2 ∨ p3) → p4)) ∨ (p4 ∧ p1)) ∨ p4) ∨ False) ∨ p4) ∨ (p2 ∨ False)) ∧ p1) → ((False ∨ True) ∨ p4)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h9 =>
            -- Conjunctions on the left can always be decomposed.
            let h10 := h9.left
            let h11 := h9.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62986738084012955873881678143 : ((p4 ∧ (p5 ∨ (((p2 ∧ (p3 ∧ ((p5 ∨ p4) → ((p2 ∧ (p2 ∨ (((False ∧ False) ∨ False) ∨ p3))) ∨ (p4 ∨ p4))))) ∧ p2) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153162407221783408069837609898 : ((p5 ∧ ((((p5 ∨ p3) → ((((p2 ∧ False) → p1) ∧ False) ∧ (False ∧ True))) → p5) → (p2 ∧ (True ∨ p1)))) → ((p1 ∨ p2) ∨ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p5 ∨ p3) → ((((p2 ∧ False) → p1) ∧ False) ∧ (False ∧ True))) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55714889269820439035874766934 : ((((p3 → (False ∨ p2)) ∨ p2) ∧ ((True → True) → ((p1 → ((p1 → p3) → ((p2 ∨ (True → (p3 → p2))) ∧ p2))) → (p5 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57343666220676246049676302559 : (((p2 ∧ (p1 ∨ True)) ∨ ((p3 ∨ (False ∨ ((p5 → p4) ∨ ((((p4 → p1) ∨ True) ∨ p2) ∧ (p1 ∨ p5))))) ∧ ((p2 → p4) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111792049815577558380069415735 : ((((p1 ∧ ((p3 ∧ True) ∧ ((p1 ∧ ((False ∧ (p4 ∨ p1)) → ((False ∨ p1) ∨ True))) ∨ (True → p4)))) ∨ (p5 ∧ p5)) ∨ False) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172326523473664869575770693623 : ((((p4 ∨ ((p5 ∧ p5) ∨ p4)) ∨ p3) ∧ ((p5 → (p3 → False)) → (p1 ∧ p4))) ∨ ((True ∨ (((p1 ∧ p2) ∨ False) ∧ (p5 ∨ p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40670021693879947217101948268 : (((((p3 ∧ ((p5 ∨ (((p5 → p1) → (((p3 ∧ p4) ∨ p3) → (p5 ∨ (p3 ∧ p4)))) ∧ p5)) ∧ p5)) → (p3 ∨ True)) → p3) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350933553863883122630475690311 : (p4 → (((p3 ∧ ((False → (((p2 → (False ∨ p3)) ∨ p1) → p2)) → ((True → p1) → (((p3 → p4) ∨ p2) ∨ True)))) → p1) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736222020382326224510762581660 : ((((False → p2) ∧ (((p4 → p4) ∧ (p5 ∧ (((p4 → True) → (True → False)) ∧ ((((p3 ∧ p5) → True) ∨ (p1 ∨ p3)) ∧ p1)))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71230394627868997946885337072 : ((((p5 ∨ (p4 → False)) ∧ (p2 ∧ ((((p1 ∧ True) ∧ (p5 → ((p4 ∧ (True → False)) ∨ False))) → ((p4 → False) ∧ p2)) → p3))) ∧ p4) → p5) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164709643461078085305253177511 : ((((p4 ∨ (((p4 → False) ∨ True) → ((p2 → p3) ∧ ((p5 → False) → p3)))) ∨ True) ∨ False) ∨ (((p5 ∧ (True → False)) → True) ∧ (True ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777694944961217559058566001547 : (((p1 ∨ ((p3 ∧ (p1 → ((p3 ∧ (True ∧ True)) ∧ p3))) ∨ ((((p1 → (((p3 → p1) ∨ (False ∨ p3)) → True)) ∧ p5) → p3) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313115658164305529218532018333 : (p3 ∨ (((((False ∨ (p1 ∧ (((p4 ∧ ((p2 ∧ True) ∨ (p2 ∨ p3))) ∧ p3) ∧ p5))) ∧ p1) ∧ (p2 → p1)) → ((p2 ∨ p4) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116921928214717293218766502725 : (((True ∧ p5) → ((True ∧ (((p1 ∧ ((p5 ∧ p4) ∨ p5)) ∧ (p1 ∨ (p1 ∨ p1))) ∨ (p1 → p5))) ∨ (p3 → (p3 ∨ True)))) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40376281320884667911383307535 : ((((((p3 ∧ (True → (False → (((((p3 ∧ (p1 → p5)) → True) → (p4 → True)) ∧ True) ∨ False)))) → p1) ∧ (p3 → p4)) ∨ True) ∨ p3) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257298222257448592863874209576 : ((p2 ∨ p3) → (p4 → (True → (p1 ∨ (p2 ∨ (True ∧ (((p2 ∨ (True → (p2 ∧ p5))) ∨ False) ∨ (False → (False → ((p3 ∨ p5) → p2)))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111784961005263508051584963648 : ((((((p5 ∨ p1) ∨ (((p2 ∧ (p1 ∧ False)) → (p1 → p5)) ∨ False)) ∧ (p5 ∨ (p3 ∧ (True → p1)))) ∨ (True ∧ p1)) ∨ p5) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148068432984181363649949561817 : (((p5 → ((p3 ∧ False) ∨ (p1 ∧ (((p5 ∨ p5) ∨ (p2 ∨ p3)) → ((False → p2) ∧ p5))))) ∨ (p2 ∨ p1)) ∨ ((True → False) → (p5 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689925577956668593054174389982 : (((((p3 → p4) → ((((p5 ∨ True) ∨ (p2 → ((False ∧ p5) ∨ p5))) → p1) ∨ False)) ∨ ((p5 → (False → (p3 ∧ (True → False)))) ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261447318655293077386573311104 : ((p5 → p2) → (((((p2 ∧ (p2 ∨ ((p3 ∧ (True → p3)) → (((p2 → p3) ∨ (p2 → False)) ∨ p5)))) ∨ p1) ∨ p5) ∨ p1) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40431148255386204044956877037 : (((((p1 ∧ (p2 ∧ ((p3 → False) ∧ ((True → (p5 ∧ p2)) ∨ p5)))) → (False ∧ (p5 ∨ ((p5 → (False → p1)) → p1)))) ∨ p3) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63277762916330800776058440250 : ((p5 ∧ ((((p5 ∨ p3) ∨ p3) ∨ p5) ∨ (p2 ∧ (p1 → ((p2 ∧ (p3 ∨ p1)) ∨ (False → (p4 ∧ (p4 ∨ ((p3 ∨ p5) ∧ p3))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601592515975669393552192230037 : ((((p3 ∧ (((p3 ∧ (p3 ∧ p2)) ∧ p3) → (((True ∧ (((((p4 → p5) → p2) ∧ p2) → p5) → True)) ∧ (p4 ∧ False)) ∧ False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_380837310116289133001382181855 : ((((((p5 ∧ p1) ∧ ((p4 ∧ (((p5 → (True ∧ (p3 ∨ ((p2 ∧ (p3 ∨ p5)) ∧ p5)))) ∧ p4) → True)) ∨ (p4 → False))) ∧ p3) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_118152533011134800067425748424 : ((False ∨ ((((p4 ∨ p3) ∧ (p3 ∨ p5)) ∨ p1) ∨ ((p4 ∧ (p2 ∨ ((p5 ∧ (p2 ∨ p1)) ∨ ((False → p3) ∧ p3)))) → p1))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68829438050070519016929174217 : ((p4 → ((p2 ∨ (p2 ∨ p2)) → (True ∧ ((p5 ∨ p3) → ((p1 ∨ (((p2 ∨ p2) ∧ ((p5 ∨ False) ∨ (p4 → p2))) ∨ True)) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159097124385080928011395772930 : ((True → (((p1 ∨ (p2 ∧ p4)) ∨ p3) ∧ (((p2 → p2) ∨ (False ∧ ((p5 ∨ p5) ∨ p5))) → p3))) ∨ ((p3 → ((True ∨ p5) → True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711461264408308955093679238924 : ((((p4 ∨ (p1 → ((True ∨ p4) → p5))) ∧ (p5 → ((((p1 ∧ ((p2 ∧ ((p5 ∧ p5) ∨ False)) ∨ p2)) ∧ (p1 ∨ p3)) ∨ False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147143399846684392776898105105 : (((p1 ∧ (((p3 ∨ (((p5 → p4) ∨ p2) ∧ ((p5 → (p3 ∨ (p3 → p3))) ∧ False))) ∧ p5) ∧ p1)) ∧ p5) ∨ (p2 → ((p4 ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196650226838863773404393774061 : ((((((p5 ∨ p5) ∨ p2) ∨ True) ∧ p4) ∧ True) ∨ ((p1 → (p4 ∨ ((((p3 ∧ (p5 → False)) ∧ (p2 ∧ (p4 ∨ p3))) ∧ False) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207293862539401457261848588210 : ((((False ∨ (False → False)) → p4) ∨ False) → (((((((p3 ∧ (True → p2)) ∧ p4) → (False ∧ p1)) ∧ p2) ∨ (p2 ∨ (p1 ∨ p2))) ∧ p5) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199377757009923879343371113497 : ((((True → (p5 ∨ False)) ∨ (p2 → p5)) ∨ True) → (((True → p5) ∨ ((p4 ∨ True) ∨ p2)) ∨ ((p4 ∧ p3) ∨ (((p4 ∧ p5) ∧ True) ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356460525626464436497581490989 : (p5 → ((((True → p3) ∧ (p2 ∨ (((p2 ∧ p1) ∨ p3) ∧ p4))) ∧ p4) → ((False ∧ (((p4 ∧ True) ∧ p1) → (p1 → (False ∧ p2)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151455970097760031180127247595 : ((((p4 → ((p3 → ((p5 ∧ ((p4 ∧ p4) ∧ p1)) ∧ p1)) ∨ (p5 → (p4 ∨ p3)))) ∧ p1) ∨ (p5 ∧ p1)) → ((True → (p4 ∨ False)) → p4)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118888083581443321556776570554 : ((True → (p3 ∧ (((p2 ∨ p4) → ((((p2 ∧ True) → p1) ∧ (p4 ∨ (p3 ∨ False))) ∧ ((p3 → (p3 ∨ p4)) → False))) ∨ False))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186404739320833979234579975914 : (((False ∨ ((((p3 ∧ (p2 → False)) ∨ True) ∨ False) ∨ p5)) → p4) → (((p1 ∧ p2) ∧ ((True → p4) ∨ p2)) ∨ ((p5 ∨ (p3 ∧ True)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((((p3 ∧ (p2 → False)) ∨ True) ∨ False) ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47024305609689037180487820814 : ((((True → (((p1 → (p5 ∧ True)) ∧ (p3 ∨ ((p4 → (p1 → p3)) ∧ ((p1 ∧ True) → p2)))) ∨ (p4 → p3))) → p3) ∨ (True ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40531285591904891695540378067 : ((((p1 ∨ ((p4 → p3) → (((p1 ∨ (((True ∧ p4) ∧ p1) ∧ (True → (p2 ∧ False)))) ∨ (True ∧ (False ∧ False))) ∨ p2))) ∨ True) ∨ p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800098090047738526433002594267 : (((p2 → (((False ∨ p3) ∨ (p4 ∨ ((p1 → (p5 ∧ ((p5 ∨ ((p3 ∧ ((False ∧ (p2 ∨ p4)) ∨ p3)) ∧ p1)) ∨ p5))) ∨ p1))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753222342439315013918677323054 : (((False ∧ ((((p3 ∨ p2) ∨ ((False ∧ (p4 ∨ (p1 → p1))) ∨ ((True ∧ ((p2 → p2) ∨ True)) ∨ (True ∨ p1)))) → p3) ∨ (p2 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166309053130169796706244700066 : ((p5 ∧ (((((((p1 ∧ p2) → ((p1 ∨ p5) → p5)) ∨ p2) → p4) ∧ p4) → False) ∧ True)) ∨ ((p1 ∨ ((p3 → True) ∨ (p4 ∧ p2))) ∨ p2)) := by
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
theorem thm_5_vars_63206772736473858884568141952 : ((p5 ∧ (((((p1 ∧ (p3 → p2)) ∨ (False ∧ p5)) ∧ (p4 → (False → p2))) → ((p1 ∨ p4) ∧ p3)) ∨ ((p2 → (False ∨ False)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150761828844046865235049057806 : ((((p5 → (p5 ∧ (p3 ∨ (True ∧ ((p4 → p5) ∧ (p1 ∧ ((True → p4) ∧ (p2 → p2)))))))) ∨ p1) ∨ True) → (((p3 ∨ False) ∨ p1) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338231772113121168318757996781 : (p1 → ((((p2 → False) ∨ (p1 → p5)) → p4) ∨ (((((p2 ∧ ((((p4 → p2) ∨ (p4 ∨ False)) ∨ p1) → p1)) → p5) → p2) ∨ True) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126129504313861310460373310195 : ((True ∧ ((((p4 ∧ False) ∨ (p1 ∧ (p1 ∧ True))) ∨ (p2 ∨ p1)) ∨ (((False → (True ∨ False)) → (p5 ∧ (p5 ∧ p3))) → p2))) → (p3 → p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148626897557721325073415657559 : ((((p5 → p5) → ((True ∨ ((p3 ∧ p4) ∧ True)) ∨ p3)) → ((p4 ∧ p1) → (((False → p5) → p2) ∧ p1))) ∨ ((False → (p5 ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708637019541395528673243543585 : (((((p3 → ((False → p4) ∧ (False ∧ p3))) ∨ False) → (((p4 → ((p1 ∧ p3) → (p2 ∧ False))) ∧ p5) ∨ (True ∨ ((p2 → p3) ∧ False)))) ∨ p3) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185179007963568653188563223745 : (((p3 → p5) → ((p3 → p2) ∨ (p2 ∧ (p3 ∨ (p1 → True))))) ∨ (((((p2 → p2) ∨ p4) ∧ (p3 ∨ ((p3 → p4) ∨ p2))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669929900443747216172667105919 : (((((p3 ∧ ((False → ((p4 ∧ p1) → (True ∧ p1))) → p3)) ∧ ((p3 ∨ p5) ∧ (p4 → (p4 ∧ (p1 ∨ p3))))) ∨ (p3 ∨ (True ∨ p2))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166528008975232313150043732497 : ((p4 ∨ (p3 ∧ (((p2 ∧ (p1 ∨ p1)) → (((True ∧ p2) ∧ p3) ∨ (p1 ∨ p1))) → p3))) ∨ (((p4 → p4) → True) ∨ (p1 ∨ (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669470657365645619981799061130 : (((((((p1 → p4) → ((p1 ∨ True) ∨ ((p5 ∧ (p1 ∨ p5)) ∧ ((False ∧ p5) → p5)))) ∧ True) → (p5 → False)) ∨ ((p1 ∨ p3) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260284476042165614899919714515 : ((p2 → p4) → (((False → True) → ((p3 ∨ p4) ∨ ((p3 → (p3 ∨ False)) ∧ (p4 ∧ (p5 ∨ ((p4 ∧ ((p1 ∨ p4) → p4)) → p1)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387040701276511090797451387582 : (((((((p2 ∨ False) ∨ ((p5 → ((False ∨ (p1 → p5)) ∧ (p1 ∨ (p4 ∧ (p2 ∧ p5))))) → p1)) ∨ False) ∧ ((p2 ∧ p5) ∧ True)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_309956427458186791462912692743 : (p2 ∨ (((((p1 ∧ p2) ∨ True) → (p4 ∧ (False ∧ (p4 → (True ∧ (p1 ∨ False)))))) ∧ (p3 ∨ p5)) → (p3 → (p4 ∧ (p5 ∨ (True ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : ((p1 ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713929128761737786939266923124 : (((((False ∨ (p2 ∧ (p3 ∨ p4))) ∨ True) → ((((((p4 ∧ ((p3 → (p1 ∧ (False ∨ p1))) ∨ p3)) → False) ∧ p4) ∧ p1) ∨ p3) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161934429513392917410634005609 : ((p1 → (p2 → ((p3 ∧ (((p5 → False) → (False ∨ p1)) ∧ ((p4 ∨ p5) → p1))) ∧ (True ∧ p4)))) → ((True → p3) ∨ (True ∨ (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41934554722412478026501098417 : ((((p1 → (True ∨ p1)) → ((((((p3 ∧ (p2 ∨ p5)) ∨ p3) → (p2 ∨ True)) ∧ (p5 ∨ p3)) ∨ ((p1 ∧ p4) ∧ p5)) ∨ True)) ∨ p4) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175142339284962891829620072194 : ((p5 ∧ ((((p5 → True) ∧ True) ∨ p5) ∨ ((p1 ∨ p4) → ((p2 ∧ p1) ∧ p3)))) → (p1 ∨ (p3 ∨ (True ∨ ((p5 ∧ p2) ∧ (p5 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40339014491031729037808955909 : (((((((False → p5) ∨ p2) → ((p4 ∧ p5) → (p4 ∧ (((False ∨ p1) ∨ p2) → (False ∨ (p5 ∧ (True ∨ p1))))))) ∨ p2) ∨ p5) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h2.left
      let h12 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h2.left
    let h17 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639217164401653092605260712277 : (((((p1 → (False ∧ (p3 ∨ p1))) ∨ (((((p4 ∨ (p5 → p1)) ∧ (True ∨ False)) ∨ (((False ∨ p5) ∨ p2) → p3)) ∨ p4) ∧ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96446993774293957770080910338 : ((False ∨ (((True ∧ (((p3 ∨ True) ∨ p1) → False)) ∧ ((False → p4) ∨ p5)) ∧ ((True ∨ p3) ∧ (p5 ∨ (p1 ∧ ((True ∨ p3) ∧ p5)))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h5.left
      let h12 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h15 : ((p3 ∨ True) ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h16 := h9 h15
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h22 =>
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h23 =>
            -- One of the premise coincides with the conclusion.
            exact h18
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h25 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h26 : ((p3 ∨ True) ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h27 := h9 h26
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h33 =>
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h34 =>
            -- One of the premise coincides with the conclusion.
            exact h29
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h5.left
      let h37 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h39 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h40 : ((p3 ∨ True) ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h41 := h9 h40
          -- False on the left can always be used.
          apply False.elim h41
        case inr h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- Conjunctions on the left can always be decomposed.
          let h45 := h44.left
          let h46 := h44.right
          -- Disjunctions on the left can always be decomposed.
          cases h45
          case inl h47 =>
            -- One of the premise coincides with the conclusion.
            exact h43
          case inr h48 =>
            -- One of the premise coincides with the conclusion.
            exact h43
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h50 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h51 : ((p3 ∨ True) ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h49
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h52 := h9 h51
          -- False on the left can always be used.
          apply False.elim h52
        case inr h53 =>
          -- Conjunctions on the left can always be decomposed.
          let h54 := h53.left
          let h55 := h53.right
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h58 =>
            -- One of the premise coincides with the conclusion.
            exact h54
          case inr h59 =>
            -- One of the premise coincides with the conclusion.
            exact h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138461763609726111058803625822 : ((p5 → (p4 ∨ (((((False ∧ p5) ∨ p5) ∧ False) → ((p3 ∧ ((p2 ∧ p3) ∧ p1)) ∨ (False ∨ (True ∨ p1)))) → p3))) ∨ (p3 → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69265037642160481970266477794 : ((p5 → ((p2 → True) ∧ ((p4 ∧ ((True ∧ False) ∨ (p5 ∧ ((p2 ∨ (False ∧ (p4 → True))) ∨ (p5 → ((True ∧ p2) ∨ p4)))))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62175546928424766736408044879 : ((p2 ∧ (p5 → ((((True ∧ p3) → ((((p4 → p1) ∧ (True ∨ p1)) ∧ (p3 ∧ p3)) ∨ p2)) ∨ (((p3 → p2) ∧ p1) → p2)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134036060815834067394958190482 : ((((((p2 → p3) ∨ (((p4 ∧ p5) ∧ p2) → (p1 ∧ (p4 ∧ p3)))) → ((True → p3) ∨ (p3 → p1))) ∨ p5) ∨ True) ∨ ((True → p5) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



