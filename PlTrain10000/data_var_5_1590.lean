variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158551160376906025942038756635 : (((p5 → False) → (p5 → (((((p4 ∧ p4) ∧ p1) ∧ p1) ∧ (((p1 ∧ p5) → p2) → p1)) ∨ p2))) ∨ (((p4 ∧ (p4 ∨ p1)) ∧ p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303864511725556372277971330200 : (p1 ∨ ((((((False ∨ ((p1 ∧ (p3 ∨ p1)) → p5)) ∨ p3) → p5) → ((p1 ∨ p1) ∧ ((p3 ∧ p5) ∧ p4))) ∨ (p5 → (p3 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65391346670784103752334978118 : ((p3 ∨ ((((p3 ∧ (False ∨ p1)) ∧ p2) ∨ p4) ∨ (p2 → ((((p2 ∨ (p1 → p4)) ∨ ((p5 ∨ (p4 ∨ p4)) ∨ p2)) → False) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44605058305431964787808553591 : (((((p5 → (p3 ∨ p4)) → (p5 ∧ (True → False))) → (((((False → False) → (p1 ∧ False)) ∧ (p4 ∨ (p3 ∨ p5))) ∧ False) ∨ p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265859376583980415561581987810 : (True ∧ (p5 ∨ (False ∨ (((((True ∧ p2) → True) ∨ ((p2 → p3) ∨ (p2 ∧ (p1 → (p3 → ((True → True) ∨ p3)))))) → p2) ∨ (False → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_160817549277472248369739761927 : ((((False → (p4 ∨ (p5 → p4))) ∨ p5) → (p3 ∨ ((False ∨ p3) ∧ ((False → (p3 → p4)) ∨ p3)))) → ((((True ∧ p5) ∨ p5) ∨ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → (p4 ∨ (p5 → p4))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135212292994486192391763912815 : ((((p5 ∧ (False ∧ (False ∧ (((p2 → (p2 → p3)) ∧ (p1 ∨ True)) ∧ p4)))) ∨ ((p5 → p1) ∧ True)) → (p1 ∧ False)) ∨ ((p3 → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319453939986710542275282531820 : (p4 ∨ (((p2 → ((p4 → False) ∨ ((p1 ∨ (False ∨ p1)) ∨ False))) → p2) ∨ ((p2 ∧ p1) ∨ (True ∧ ((p2 → True) ∨ ((p4 ∨ p4) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198402602720835598477051266015 : ((p4 ∧ (((p5 ∧ (p4 ∧ p2)) ∨ False) ∧ p1)) ∨ (((p4 → p1) ∧ (True ∨ (p5 ∨ ((True ∨ False) → ((True ∧ p1) ∨ p3))))) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743739714777655651810120907093 : ((((True ∧ p4) → ((((p1 ∧ ((p1 ∨ False) ∧ False)) → False) → ((p5 ∨ (p2 ∧ p5)) ∨ ((p2 ∧ False) ∨ (p4 ∨ (p4 ∨ True))))) ∨ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200867141680748678488936583289 : ((True ∨ (p3 → (False → ((p4 → p1) ∨ False)))) → (((p4 ∧ (True ∧ ((p2 → p5) → (p3 ∨ True)))) → p1) ∨ (False → ((p1 ∨ True) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48412633258629065986429804459 : (((p2 → (((((((p5 → p1) ∨ (p5 ∨ p4)) → (False ∧ (p1 ∨ False))) → (True ∧ p5)) ∧ p4) ∨ p5) → (p3 → p4))) → (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738629901016568170410132316817 : ((((p2 ∧ False) ∨ ((False ∨ (((((p4 → p4) ∨ p1) → p4) ∧ (((p3 ∨ p1) → (False ∨ p2)) ∧ (p3 ∧ True))) ∧ False)) ∨ (p5 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121803515886106212404828946551 : ((((p4 ∨ (p1 ∨ p3)) → ((True ∧ False) ∨ ((False → (((p5 → p3) → (p4 → p5)) → False)) → ((False ∧ p2) → p3)))) → False) → (False ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ (p1 ∨ p3)) → ((True ∧ False) ∨ ((False → (((p5 → p3) → (p4 → p5)) → False)) → ((False ∧ p2) → p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h2
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191327480364696815657700999015 : (((p2 ∧ p2) ∨ ((p3 ∨ p5) ∨ ((p2 ∨ p3) ∧ p1))) ∨ (True ∨ ((((p4 → True) ∧ ((p3 ∧ False) ∧ False)) ∧ p4) → (True ∧ (False ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149701228076083514609295044029 : ((p5 ∧ ((p3 → (True → True)) → (False ∨ (p3 ∧ ((p5 ∨ (p3 → ((p4 ∧ (False → p2)) ∨ p5))) ∧ p3))))) ∨ (False → (True ∨ (p3 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260804371251105455855643082787 : ((p3 → p5) → ((p3 → p3) → (p4 ∨ (p4 → (((p5 ∧ False) ∨ (True ∨ p2)) ∧ (((p2 ∧ p3) ∨ ((p1 ∧ (False ∧ True)) → p5)) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60109994223978243566827158402 : (((p3 ∨ p3) → ((((False → True) ∧ (((p3 ∨ p5) ∨ True) ∨ (p1 ∧ ((p4 → True) → ((False ∧ (True ∧ True)) ∧ p5))))) ∨ p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246574408007573830294954393494 : ((p5 ∧ p2) ∨ ((((((p4 ∧ ((p1 ∧ p2) ∨ p5)) ∧ p5) ∨ (True → True)) ∨ (p5 ∨ p1)) ∨ (False → p4)) ∧ ((True ∧ (p2 ∧ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75857963873617630239946697019 : ((((p5 ∧ (p4 ∨ ((((p4 ∨ (False ∨ p5)) ∨ (((p1 ∧ p3) ∨ (True ∨ (p5 ∧ p3))) ∨ p4)) → p1) ∧ (p3 ∧ True)))) ∨ True) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (p4 ∨ ((((p4 ∨ (False ∨ p5)) ∨ (((p1 ∧ p3) ∨ (True ∨ (p5 ∧ p3))) ∨ p4)) → p1) ∧ (p3 ∧ True)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609012022445822663865829051924 : ((((((p3 ∧ ((((p1 ∨ p4) ∧ (False → True)) ∨ False) → p1)) ∨ ((p1 → p2) ∨ ((True ∧ True) → (True → (p4 → p1))))) ∨ p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2494959362264232141364104473 : (((True → p2) ∧ ((((p4 ∧ False) → p1) ∧ p3) ∧ p1)) → ((p2 ∧ True) ∧ ((p2 ∨ (p2 ∨ (((p5 ∨ False) → False) ∨ False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683755012147775770364041146463 : (((((((((False ∧ p5) ∨ ((p4 → p5) → (False → True))) → p3) → (p5 ∨ p5)) ∨ True) ∨ p3) ∨ (p1 ∨ ((True ∧ (p1 ∧ False)) ∨ p2))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_655885130982214546781796702099 : (((((True ∨ (((((((p4 ∨ True) ∨ p1) ∧ p2) ∧ (True ∧ True)) → True) ∨ p3) ∧ (p2 ∧ p3))) → (False ∧ (p4 ∧ p3))) ∨ (p1 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151778055523652546217700156238 : ((((p2 ∨ p4) ∨ (True ∨ ((p3 → (p4 ∧ (False ∨ False))) ∨ (p3 → (p4 ∨ p5))))) → (p5 ∨ (p3 ∨ p4))) → (((p2 → p5) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305009600676217266710672413875 : (p1 ∨ ((((((p2 ∨ p5) ∨ p5) ∨ p5) ∧ False) ∧ ((False ∧ False) → ((((p4 ∨ p1) ∧ (True ∨ p4)) ∨ False) ∨ True))) ∨ ((False → False) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149520836798698860348546476178 : ((p1 ∧ (p3 ∧ (((p3 → p5) → ((p4 → ((p3 → False) ∧ (p4 ∧ (p2 ∨ (True → p1))))) ∨ False)) ∧ p1))) ∨ (True ∧ ((True ∨ p3) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49325025200913396265255971788 : (((p4 ∨ ((((p1 → (p2 ∨ (((p3 → p4) ∧ p5) ∧ True))) ∨ (p3 ∧ True)) → p1) ∧ ((p1 ∧ False) → p4))) ∨ (False ∨ (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147312430189607972863909161706 : ((((True ∧ (((p4 ∧ ((p3 → ((False → p5) ∨ p2)) ∨ (p3 ∧ p2))) ∨ (False → p4)) → p3)) → p4) ∨ p4) ∨ (p3 → ((False ∧ p5) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40305608829032377639169796476 : (((((((True ∨ p2) ∧ (((p4 ∨ ((p1 ∨ (p5 ∨ p2)) → p4)) → p3) ∨ ((p2 ∧ p5) ∧ p2))) ∨ (True ∨ p1)) ∧ True) ∨ True) ∨ p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41749408378315873113135605229 : (((((p2 ∨ (False → True)) ∧ p1) ∨ (p5 ∧ ((((p3 → (p3 → (p2 → p3))) ∨ p5) ∧ p2) → ((True → True) → (True → False))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191752750348343243562573663292 : ((False ∨ (p1 ∨ (p5 → (p2 ∧ ((p2 ∧ False) ∨ False))))) ∨ (((((p4 ∧ (False ∧ True)) ∧ (p5 ∧ p1)) ∧ (p1 → False)) → p3) ∧ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201025790019462171675116746752 : ((p4 ∨ ((False ∨ ((p5 ∧ p2) ∧ p1)) ∨ True)) → (((((((False ∨ p4) ∧ (False → p1)) → (False ∨ p5)) → p3) → p4) → False) ∨ (True ∨ False))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111562851654348308847891892408 : (((((True ∧ (((p1 → p4) → True) ∧ (p4 ∧ True))) → (((p1 ∨ p3) ∨ p3) → (((False ∧ p1) ∧ p2) ∧ p2))) ∧ True) ∨ False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775368232568431408887443832915 : (((False ∨ (p1 ∧ ((p3 → (p4 ∧ ((p3 → (((p3 ∨ p2) ∧ False) ∧ ((p5 ∨ p3) ∨ ((p5 → True) ∧ False)))) ∧ (p3 → p4)))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147892277886590858439366856399 : ((((((p4 → (((p1 ∨ (False ∨ p1)) ∨ False) ∧ False)) ∨ ((p2 → p1) ∨ False)) ∨ p3) ∨ p3) ∧ (p3 ∨ p2)) ∨ (((p5 ∨ False) ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221197055166082127437137083320 : (((p1 ∨ True) ∨ p5) ∧ ((((p3 → (False → (((p1 ∧ False) → ((p3 ∧ p2) → (True ∧ p1))) ∧ p4))) ∨ p2) → p5) → (p5 ∧ (p1 ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → (False → (((p1 ∧ False) → ((p3 ∧ p2) → (True ∧ p1))) ∧ p4))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- False on the left can always be used.
    apply False.elim h10
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : ((p3 → (False → (((p1 ∧ False) → ((p3 ∧ p2) → (True ∧ p1))) ∧ p4))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h15.left
    let h20 := h15.right
    -- False on the left can always be used.
    apply False.elim h20
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h12
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167172552358165851102477985641 : ((((p1 ∨ p2) ∨ (p2 ∧ (False ∧ (True → ((p2 ∧ (p5 ∨ (p1 ∨ p4))) ∧ True))))) ∨ p1) → ((True ∧ (p1 → (True → p2))) → (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h8 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h9 := h4 h8
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h11 := h9 h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h18 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h19 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h20 := h4 h19
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598517428869408477610791777111 : ((((((p3 ∧ p5) → p4) → ((p2 ∧ (p1 → ((p5 → p3) → ((p3 ∨ (False ∧ p1)) ∧ ((p2 ∨ p5) ∧ False))))) ∧ (False ∧ p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661225552807890264874439025994 : ((((((p5 → False) ∨ ((((((True → (False ∨ p1)) ∨ (p3 → (True ∨ p5))) → p1) → p4) ∨ p1) ∨ p1)) ∨ (False → p2)) → (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685801066213951335374104758835 : ((((((p3 ∨ ((p2 ∧ (((p4 ∨ p4) → (p2 ∨ p1)) ∧ p3)) ∧ p3)) ∨ (p2 ∧ p3)) → p3) → ((((True ∧ p1) ∨ p2) → p5) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115241128388588948521011117478 : ((((True ∨ (p4 ∧ (p3 → (p1 → (True ∨ p5))))) → p1) ∨ ((((p5 ∨ ((True ∧ p2) ∧ (p5 ∨ True))) ∨ p3) ∧ p1) ∨ p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225729311073587945309143467940 : (((p4 → False) ∧ p5) ∨ ((((True ∧ (p5 → ((True → p2) ∧ p2))) → (p3 ∨ p2)) → ((p3 ∨ p4) ∧ p5)) ∨ (((True ∨ True) ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42738627129722796741856676947 : (((True → ((p5 ∨ (((p1 → p5) ∧ (p4 ∧ (False ∨ (p2 → p3)))) → ((p4 ∨ p3) → p3))) ∨ (p1 ∨ (p3 → (False → p4))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325916993238990897013763346494 : (p5 ∨ (p5 ∨ (((p5 ∨ ((p1 → (p4 ∨ p5)) → (p2 → True))) ∧ ((True ∧ (((p5 → ((p3 → p3) → p1)) ∧ p1) ∨ True)) ∨ p3)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_152781340293346729657273660677 : (((p1 ∧ p3) → (((False ∧ ((((p2 ∧ p2) ∨ False) ∧ p5) ∨ ((True ∨ p5) ∨ p5))) → p3) ∧ (p4 ∧ p5))) → ((p4 → False) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173076770207480312938473443686 : ((p1 ∨ ((p3 ∧ ((p4 → (((False → (p1 ∨ False)) ∨ p4) ∧ False)) ∧ p1)) ∧ True)) ∨ (p2 ∨ ((((True ∨ p2) → (p1 ∨ True)) ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664207976630497981878920158946 : ((((False ∨ (p5 → ((p1 ∨ (True ∨ ((True ∧ p2) ∧ ((True ∧ (p4 ∨ False)) ∨ True)))) ∨ (p2 ∨ (p4 → (True → p2)))))) → (p5 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264981320776386646313548809410 : (True ∧ ((True → False) → ((p3 ∨ p4) ∧ ((p4 ∨ p4) ∧ (p2 → ((False ∨ p5) ∧ ((((True → (p3 ∧ True)) → False) ∨ False) → (p1 ∧ p1)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608834724616254432478192963743 : (((((((p4 ∨ (((False ∨ p5) ∨ p3) ∧ p3)) → (True ∧ ((p3 ∧ (p4 ∨ p2)) → p5))) ∧ (p1 ∧ (p1 → (p5 ∧ p4)))) ∨ True) ∨ False) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_159890101650580112787675406058 : ((((((p2 ∨ ((((False ∨ p1) ∧ (p3 ∧ p1)) ∧ p4) ∨ (p2 ∨ True))) ∨ p1) ∨ p5) ∨ p1) → False) → (p4 → (((p5 ∧ False) ∨ p3) → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : ((((p2 ∨ ((((False ∨ p1) ∧ (p3 ∧ p1)) ∧ p4) ∨ (p2 ∨ True))) ∨ p1) ∨ p5) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304982737219492960172507617656 : (p1 ∨ ((((p1 → (p4 ∨ ((False ∧ True) → (((p3 → (p1 ∨ ((p5 ∧ p2) ∨ p5))) ∧ p1) ∨ False)))) → p4) ∨ True) ∨ (False ∧ (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313005352464812457244000395931 : (p3 ∨ (((((False ∨ p5) → (p1 → (((True ∧ p5) ∧ p3) ∧ ((p4 ∧ (True → (p2 ∧ p3))) ∨ p3)))) → (p4 → (False ∨ p2))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111610941008126796005571202668 : (((((((p4 ∧ (False ∨ p5)) ∨ p5) ∨ (((((p3 → True) → p3) → False) ∨ p2) ∨ ((True ∨ False) ∨ p3))) ∨ p1) ∨ p4) ∨ True) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211434465391339371400522752589 : (((p4 → p4) ∨ (False → True)) ∧ (((p4 ∧ (p3 ∧ p1)) ∨ True) → ((p2 → False) ∨ (p2 ∨ (p3 ∨ (((p4 → p2) ∨ p3) ∨ (p4 ∨ True))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140144605327495090271616408292 : ((((p4 → (p5 ∨ ((p4 ∧ (p5 → (((p5 ∧ p3) → p1) ∧ (p2 ∨ p5)))) → (True → p1)))) ∨ False) → (p2 ∧ False)) → (p1 ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21513202910825649391571525567 : ((((p5 ∧ p4) ∨ (True ∧ (((p5 ∧ True) ∨ p5) ∧ False))) ∨ ((((False ∨ (p5 ∨ (p4 ∨ False))) ∧ p4) → (True ∨ (True → p1))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_725186881726992317871213876124 : ((((p2 → (p2 ∧ True)) ∧ ((((((p4 → (((p4 ∧ False) ∨ True) → p2)) → p2) ∨ (p3 → p4)) ∨ True) ∨ (False ∧ p3)) ∧ (p1 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158882614293073703147175730429 : ((False ∨ (p5 ∧ (((((p4 ∨ p1) ∨ p1) ∧ p2) ∧ (p4 → (True → False))) ∨ ((p4 → p5) ∨ p3)))) ∨ ((((p2 ∨ True) ∧ False) → p2) ∨ p3)) := by
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
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184844243276897108846578317000 : (((p3 ∨ (False ∧ (True → False))) → (((True ∨ p3) → p5) ∨ p1)) ∨ (((True ∨ (p5 → p4)) → (p1 ∧ p4)) → ((p1 ∨ (p5 ∨ p1)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p5 → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ (p5 → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207137863868315757387621492862 : (((True → (p2 → (p5 ∧ p2))) ∧ p4) → ((((p1 → (p4 → (p4 → p3))) ∧ p3) ∨ (((p3 ∨ True) ∨ True) → p3)) ∨ ((False ∨ True) ∨ False))) := by
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
theorem thm_5_vars_137000689758900885943374531352 : (((False ∨ True) → (p5 ∨ (p1 ∧ (p1 ∧ (((p1 → ((False ∨ p3) ∧ p3)) ∧ p3) ∧ (p2 → ((p4 ∧ p4) → p2))))))) ∨ (True ∧ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675013128619512154214468394907 : (((((False ∧ ((((((True ∧ False) ∨ (p3 ∧ ((p1 ∧ p3) ∨ p5))) → True) ∧ p5) → p3) ∧ p1)) ∧ p3) ∧ ((True ∧ p3) ∨ (True ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745876522044363009662599103909 : ((((False ∨ p2) → ((((p4 ∨ (False ∨ p4)) → (((True → False) ∧ p1) ∨ True)) → ((p4 ∧ p4) → p3)) → ((p1 ∨ p4) ∧ (p1 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67926053697197273538489017409 : ((p2 → ((((((True ∨ p3) ∧ (p5 ∨ p1)) ∨ p5) ∨ p3) → p5) → (((p2 → (p5 ∧ p2)) → p3) ∨ (True → (True ∨ (p5 → p1)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228833374975331625361147531033 : ((p3 ∨ (True → p5)) ∨ ((((p2 ∧ (p2 ∧ p4)) ∧ p4) → False) ∨ (p1 ∨ ((p5 ∨ True) ∧ (p1 ∨ (p2 ∨ (False → (True → (p4 ∧ p3))))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
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
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173006037793253797481018024705 : ((p5 ∧ (False ∧ ((((((p2 ∨ p2) ∨ p5) ∨ False) ∨ p4) → (True → True)) → p4))) ∨ (p5 → (((False ∧ True) → p2) ∨ ((False → False) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65105965865445446863600921312 : ((p2 ∨ (p4 ∨ ((p2 ∧ (((p3 ∧ (p3 ∧ p1)) ∨ (p2 ∨ ((p2 ∧ ((p4 → (p1 ∨ (False ∨ True))) ∨ True)) ∧ True))) → p4)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158184385367877215265022106336 : (((True ∨ (p5 ∧ (p2 ∨ p3))) → (((((False ∨ p1) ∨ (p2 → (p2 → p1))) → p5) → p1) ∨ p2)) ∨ (p4 → ((p3 ∨ (p2 → True)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68361079045848362037091902123 : ((p3 → ((((p2 ∧ (p3 ∨ p2)) → p1) ∨ (p5 → False)) → ((((False ∨ p5) → (p1 ∨ p5)) ∧ p1) ∨ ((True ∧ p3) → (False ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42135608713767552192565722499 : ((((p3 ∨ p1) → (p4 ∨ ((((p5 ∨ p2) → p2) ∨ ((False ∨ (p1 → True)) → (True ∧ p5))) → (p2 ∧ ((False → p1) ∧ p5))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787902839818745111510580080151 : (((p4 ∨ (p3 → (((p3 ∨ (p3 → p5)) → (p5 → ((((p1 ∨ p4) ∨ False) ∧ ((p1 → p3) ∧ p5)) → (p1 ∨ p2)))) ∨ (p3 → True)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320489033140386675853484051100 : (p4 ∨ ((p4 → p4) → ((((True ∧ (((((p3 ∨ (p2 ∨ p4)) ∨ p3) ∨ p2) ∧ p3) → p3)) → False) ∨ p1) → (((p2 ∧ True) ∨ p1) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True ∧ (((((p3 ∨ (p2 ∨ p4)) ∨ p3) ∨ p2) ∧ p3) → p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- One of the premise coincides with the conclusion.
              exact h7
            case inr h13 =>
              -- One of the premise coincides with the conclusion.
              exact h7
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h4
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115310266215560685386438179312 : (((((((p4 ∨ p1) ∧ p3) ∧ True) ∨ p5) → (p2 ∨ True)) → ((p5 ∧ False) ∨ (p3 → (((p1 → p1) ∨ (True → p4)) → False)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82160139829006807060645125235 : (((True → (((True ∧ (p2 → (((p3 ∨ (True ∧ (p5 → p3))) ∧ p5) ∧ (p2 ∨ (p3 → p1))))) → p3) ∨ True)) → (p2 ∧ (True ∨ p1))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (((True ∧ (p2 → (((p3 ∨ (True ∧ (p5 → p3))) ∧ p5) ∧ (p2 ∨ (p3 → p1))))) → p3) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111893037408152377383736298681 : (((((((p4 ∨ True) → False) ∧ ((False ∧ ((False ∧ p5) ∧ p3)) → p2)) → p4) ∨ ((p4 → p2) → ((p2 ∧ False) → False))) ∨ p1) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20430649123665034519564983642 : (((((((p3 → True) ∧ p3) ∨ (p1 ∨ p2)) ∧ p5) ∧ ((p5 → p1) ∧ p1)) → (p1 → ((((p1 → p2) → p4) → p4) ∨ (p2 → True)))) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h4.left
      let h16 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h4.left
      let h20 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650330415525467864971975073316 : (((((((True ∨ p3) → ((p3 → False) ∨ p5)) → ((p1 ∧ (False ∧ p4)) ∧ p5)) ∧ (p4 ∧ (p4 ∧ (p3 → (p2 ∨ p1))))) ∧ (False ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349049042488622156106594058460 : (p3 → (p5 ∨ ((True ∧ (((False ∨ (p1 ∨ (p5 → p3))) → (p1 ∧ p2)) ∧ ((p2 ∨ (p1 → False)) ∨ p2))) ∨ ((p5 → True) ∨ (False ∧ p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53979941890302007468226282686 : ((((((p4 ∧ p3) ∨ (p1 ∨ (p3 → p2))) ∨ True) ∨ p3) → ((p3 ∨ (False ∨ True)) ∨ ((p1 ∧ False) ∨ ((p5 → p4) ∧ (p1 → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135142323910782119937537011058 : (((p2 ∨ (True → ((((((p2 ∧ p4) ∨ (p4 ∨ p3)) → p2) → (p3 ∧ p2)) ∨ p3) ∧ (p2 → p2)))) ∨ (False → p5)) ∨ ((p1 ∨ p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230594027076212765306717637258 : (((p1 → p5) ∧ True) → (((p4 → ((p2 ∨ (p1 ∨ (p3 ∨ ((p5 ∧ p4) ∧ False)))) ∧ ((p4 ∧ True) → (p3 ∧ p5)))) → p3) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740276138408485873794407547061 : ((((p1 ∨ False) ∨ (((p5 → (p4 → False)) ∨ (((p1 ∨ p3) ∨ (p3 ∧ (True → ((((p5 ∨ False) ∧ p2) ∧ p1) ∧ p5)))) ∧ True)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1963486637791876594388994961 : ((((p2 ∧ p5) ∧ p2) ∧ (p3 ∧ (((p4 ∧ False) ∨ (((p3 ∨ True) ∧ p2) ∨ (True → p5))) ∨ p2))) ∨ (((p2 ∧ p5) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612841070691336092947708103352 : (((((False ∧ ((True → p2) ∨ ((False ∧ p4) ∧ ((((False ∨ True) ∨ (p4 ∨ p1)) ∧ ((p3 ∧ False) ∨ p1)) ∨ p2)))) ∨ (False → p2)) ∨ p1) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_780400403900865651446497223430 : (((p2 ∨ ((((((True ∧ p2) ∧ p2) ∨ p2) → (p3 → p4)) → (((True → p4) ∧ False) ∨ p2)) ∨ ((True ∧ False) → (p2 → (p5 ∨ p2))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230491478236708303206785296160 : (((True → False) ∧ p4) → ((p3 ∨ True) ∧ (False ∨ ((False ∧ p3) ∧ (((True → ((False ∨ p3) ∧ False)) ∧ p1) ∨ ((p1 ∨ (p1 ∨ p2)) → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337364907977774228050890202824 : (p1 → ((((((p2 → p3) ∧ (p5 ∧ ((p4 ∨ p3) ∨ p1))) → (True ∨ False)) → p3) → (p4 ∨ ((p2 → p5) → p5))) ∨ ((p3 ∧ p4) → p4))) := by
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
theorem thm_5_vars_701826253286959069314357739476 : ((((p4 ∧ ((p4 ∨ p4) ∧ ((p5 → p4) ∧ (p3 → p2)))) ∧ ((p3 → (p1 ∨ (p1 ∨ (True → ((p4 ∨ (True ∧ p1)) ∧ p2))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198718126356696996375475752681 : ((p5 ∨ (((p5 → True) ∨ p3) → (p5 ∨ False))) ∨ ((((p1 ∨ False) → (False → (p3 ∨ (p2 ∧ p2)))) ∧ p2) → ((True ∨ (False ∨ p4)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315136163821687404441733536804 : (p3 ∨ ((p2 ∨ (p5 ∧ (p1 ∨ (p4 → p3)))) ∨ ((((p1 → (True → p4)) ∧ ((((True → p4) → (p2 ∨ True)) ∨ True) → False)) ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342174955262991343548662670780 : (p2 → ((p4 ∧ (((False → ((p4 ∨ (True → p3)) ∧ (p2 ∧ p2))) ∨ True) → (((p2 ∨ True) ∧ p3) ∨ p4))) ∨ ((p1 → (p3 → p1)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337090012984359977543412168968 : (p1 → ((((((True ∧ p3) ∨ p3) ∨ p5) ∨ ((p4 → False) ∨ (p2 ∧ p3))) ∨ ((p1 ∨ p2) ∨ ((False ∨ (p1 ∧ True)) → p3))) ∨ (p1 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254904249293872034927701589072 : ((p4 ∧ True) → (((False → p2) ∨ (False ∨ (p5 ∨ p1))) → (((p4 ∨ ((p3 ∨ p2) → (p2 → p4))) → (p3 ∧ (False ∧ (False → p1)))) → p1))) := by
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
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ ((p3 ∨ p2) → (p2 → p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : (p4 ∨ ((p3 ∨ p2) → (p2 → p4))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h18 := h3 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257947744009995016596500435897 : ((p4 ∨ False) → ((False ∨ p3) ∨ (((p5 ∧ p4) → (p1 ∨ ((p2 ∧ ((True → (p5 ∧ p5)) ∨ (p1 ∨ ((p3 ∨ p3) ∧ p2)))) → p3))) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65362587586955301609146449157 : ((p3 ∨ ((p2 → (False ∨ (p4 ∧ (((p3 ∨ False) ∧ p1) ∧ (p1 → p4))))) ∧ (p4 → (False → ((p1 ∨ True) → (p3 ∧ (True ∧ p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774800262493911114000619783088 : (((False ∨ (((True → ((p1 ∨ False) ∨ p2)) ∧ True) → ((((((False ∨ p3) ∧ (p4 ∨ p1)) → p5) → p5) ∨ (True ∨ (True ∧ p3))) ∨ p5))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167386078426500272603780982982 : (((((p3 ∧ p2) ∧ True) → (((p1 ∨ p2) → p1) → ((p1 ∨ p3) → (p3 ∨ p5)))) → p4) → ((p3 → (p2 ∨ True)) → ((p2 → p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∧ p2) ∧ True) → (((p1 ∨ p2) → p1) → ((p1 ∨ p3) → (p3 ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h4.left
      let h9 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354900425061982183575554870633 : (p5 → ((p5 ∧ ((p1 ∧ (p1 ∨ ((((p3 ∧ (p4 ∧ p1)) → (p1 → p4)) → ((p2 → p3) ∨ p1)) ∧ (False ∨ p1)))) → (p5 → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148072437178747005687799258552 : ((((((False → p4) → (p3 ∨ (p5 ∨ ((p5 ∨ p2) → p2)))) ∧ (p2 ∨ (p1 → p5))) ∧ p4) → (p3 ∨ p2)) ∨ (((False ∧ p2) → p3) ∨ False)) := by
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



