variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113057616582539843140587260154 : (((p2 ∨ (((p4 → (True ∨ (p3 ∨ (p1 → ((p4 ∨ p5) ∧ ((False ∨ p5) → p2)))))) ∧ (p5 → p1)) ∧ (p5 → p1))) → p5) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351464051343852193791712761546 : (p4 → (((p1 → p5) → (((p5 ∨ (p4 ∨ ((p2 ∨ p2) ∧ p5))) → (p5 ∧ (p4 ∨ (p3 → False)))) → p4)) → ((p5 ∨ p4) ∧ (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340831499383312896573179521659 : (p2 → ((((True ∧ (p3 → (((p1 → ((p2 ∧ p3) → (p5 ∧ False))) → (p1 ∨ p3)) → (p4 ∧ (p1 ∧ p2))))) → p2) → (p1 ∨ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60856692944884874135376184676 : ((True ∧ (p4 ∨ (((p5 ∨ ((p3 → ((p1 ∧ p3) → p1)) ∨ ((False ∨ p2) ∧ (p1 ∧ (p1 ∨ p4))))) ∨ True) → (p1 ∧ (p1 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309331213461376432347264373389 : (p2 ∨ (((p1 ∨ (p4 ∧ ((True ∧ ((p2 → p2) ∨ True)) → (False ∧ (p3 ∧ (p2 ∧ (p4 → (p3 ∨ False)))))))) ∧ (False ∨ p2)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730157315411984027972360423355 : (((((p5 ∨ p3) → p5) → (p2 → ((p5 ∨ (((False ∨ False) ∧ ((False ∧ p3) ∧ ((False ∨ (p4 → p2)) ∧ p2))) ∨ p2)) → (p4 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335704259067233824928757359994 : (p1 → ((((p4 ∨ (p2 ∨ p5)) ∨ ((p3 ∧ ((False ∨ (p1 → ((p5 ∧ p2) ∨ (p5 → p4)))) → (p5 ∨ (True ∧ True)))) ∨ p4)) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56429507415323028267315228023 : ((((p5 ∨ p3) ∧ (p4 → p1)) → (((((False ∧ (True → p3)) ∧ (p3 ∨ (True ∧ (True ∧ p3)))) → (p4 ∧ False)) → (p4 ∧ False)) → p2)) ∨ p3) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (((False ∧ (True → p3)) ∧ (p3 ∨ (True ∧ (True ∧ p3)))) → (p4 ∧ False)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
      -- Conjunctions on the left can always be decomposed.
      let h12 := h7.left
      let h13 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h6
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h19 : (((False ∧ (True → p3)) ∧ (p3 ∨ (True ∧ (True ∧ p3)))) → (p4 ∧ False)) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- False on the left can always be used.
      apply False.elim h23
      -- Conjunctions on the left can always be decomposed.
      let h25 := h20.left
      let h26 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- False on the left can always be used.
      apply False.elim h27
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h29 := h2 h19
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221001455139950525050679075239 : (((p3 ∧ False) ∨ True) ∧ (p5 ∨ (((p2 → (p1 ∧ p5)) ∧ (False ∧ (((((p1 ∧ p1) ∨ (p4 ∧ p3)) → p2) → p3) ∧ p3))) ∨ (False → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256896539076704344857482912819 : ((p1 ∨ p4) → (((p2 ∨ (True ∧ (p4 ∨ (p5 ∨ (p2 → (((p4 ∨ (p5 ∧ True)) ∧ p3) ∧ (p4 ∨ p4))))))) ∧ p3) ∨ (p4 → (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800223145761099171831682335296 : (((p2 → ((((((p4 ∨ (p3 → p5)) ∧ ((False ∧ p1) ∨ False)) ∧ (True → (p5 → False))) ∧ (p3 → ((True ∧ p1) ∨ p5))) ∨ p2) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798250315612570870502665067142 : (((p1 → (((p2 → ((p3 ∨ ((p1 ∨ p2) → ((False ∨ (p1 ∨ p5)) → p5))) ∧ p4)) → False) ∨ (((True ∧ p1) → (p3 ∧ True)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355874835331739386911578191932 : (p5 → (((p2 ∨ p2) → (p3 ∨ (((((p4 → p1) ∧ (p2 ∨ p5)) ∧ p2) → p4) ∨ ((p3 ∧ (True ∨ p1)) ∧ p3)))) ∨ (p4 ∨ (p2 → True)))) := by
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
theorem thm_5_vars_52513618530148188725129059158 : (((((p4 ∨ True) → ((True ∧ ((False ∧ True) ∧ p5)) ∨ (True ∧ p2))) ∧ p2) ∨ (p5 → ((((True → p2) → (p1 ∧ p5)) → p3) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323209734332469108577061861834 : (p5 ∨ (((((p2 → (p1 ∨ (p3 → p3))) ∨ p5) ∧ ((((False ∧ True) → p3) ∨ p3) → (p3 ∨ p5))) ∨ (False → (p4 ∧ False))) ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733519045223117778034854017028 : ((((p4 ∧ p3) ∧ (((True → p1) ∧ (((p3 → ((True ∨ p4) → p3)) ∨ False) ∧ p2)) → (False ∨ (((p1 ∧ True) ∨ False) ∧ (p3 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174826178867718541781221800555 : (((False ∧ p4) ∨ (True ∧ (p1 ∨ (((p5 → (True ∧ (True → p1))) ∧ p2) ∨ p2)))) → ((False ∨ (p2 ∨ ((p2 ∨ False) ∧ p5))) ∨ (p3 → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166485399691788037462718619636 : ((p3 ∨ ((((p2 ∨ ((p4 ∧ p5) → False)) ∧ p1) ∨ False) ∨ (((False ∨ p2) ∨ p2) → p2))) ∨ ((((True ∧ True) ∨ (False ∨ p1)) ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185550465765567575651743242685 : ((p4 ∨ (((True ∧ (False → p2)) → (False ∨ (p3 ∧ p4))) ∨ False)) ∨ (((((p5 ∨ p4) → p2) → p3) ∨ (p5 ∧ True)) ∨ (False → (p1 ∧ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52454525976869299080149870091 : (((p5 ∧ (((p5 → (p2 ∨ p2)) ∧ (p5 → (p4 ∨ (p5 ∧ p2)))) ∧ p1)) ∧ ((p2 → p1) ∨ ((True ∧ p1) ∨ ((p1 ∧ True) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620426185118170959076893064511 : (((((p5 ∨ p2) ∨ ((False → (p1 ∧ (True ∧ ((((True → False) ∨ p3) ∧ (p1 ∧ p3)) → True)))) → (p3 ∧ ((p5 ∨ True) ∨ True)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_301747941661465543554148512973 : (False ∨ ((p2 → p2) ∧ (((p1 ∨ p4) ∧ (p1 ∧ p4)) ∨ (p4 ∨ (False → ((p3 ∨ ((p3 ∨ p3) ∨ (False → (p5 → (p5 ∨ p2))))) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49225941260865804514051826000 : ((((p3 ∧ p5) ∨ ((p5 → (((p4 ∨ True) → (p1 ∨ ((True ∨ (p5 → p5)) ∨ (p5 → p2)))) ∧ p5)) → p5)) ∨ ((p5 → p1) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727366179328392235966111774801 : ((((p2 ∧ (False ∨ False)) ∨ (True ∧ (((p3 ∧ p4) → (p4 ∨ (((p1 → (p2 ∨ p5)) ∧ (True → False)) ∧ False))) → ((p3 ∧ p4) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248286746201081722724576082110 : ((p2 ∨ p2) ∨ ((p5 ∨ (p3 ∧ (p5 → False))) → (p4 ∨ ((p3 ∧ (p1 ∧ ((True ∨ False) ∧ p1))) ∨ ((((p1 ∧ p4) ∨ p5) ∧ p2) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150486366126711253683047749916 : ((((((p1 ∨ p5) ∧ (p2 → (p5 ∨ (((p1 → p4) ∧ (p1 ∧ p2)) ∨ False)))) → p5) → (p5 ∨ p1)) ∧ p1) → ((p4 ∧ p5) ∨ (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142436536924922858001273792056 : ((p4 ∧ (p5 → (((p4 ∧ (p2 ∨ (((p5 ∧ (p3 ∧ (False ∧ False))) ∧ (p5 → p4)) → False))) ∨ (p1 ∨ p3)) → True))) → ((p1 → p2) ∨ True)) := by
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
theorem thm_5_vars_654655836559648708672574335026 : (((((((p1 ∨ ((p5 ∧ True) ∨ ((((((p3 → p4) ∧ (False ∨ p2)) ∧ p5) ∧ p1) ∧ p4) → p5))) → True) ∧ p1) → p5) ∨ (p5 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337774203345392262115134334883 : (p1 → (((p1 ∧ False) ∨ ((True ∨ p2) → (p5 ∨ ((p5 → (p4 ∧ (True ∨ p5))) ∧ p2)))) ∨ ((p1 ∨ (p2 ∨ (p1 ∨ p2))) → (p3 ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233244595223291965108468044729 : ((True ∨ (False ∧ p1)) → (p5 ∨ ((False → False) ∧ ((((p5 ∧ p5) → (p4 ∨ p2)) ∧ (True ∧ ((((p5 ∨ False) ∨ p2) → p4) ∧ False))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40446098904273015627132780761 : ((((((p3 ∨ (True ∧ p2)) → (p3 ∧ p2)) ∧ (((p3 ∨ p1) → (((False ∨ (p2 ∧ p4)) ∨ p4) ∧ p3)) ∧ (False → False))) ∨ True) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206419916751690191782064072874 : ((p3 ∨ (p3 ∨ (p4 ∧ (p1 ∨ p5)))) ∨ ((False → ((((p1 ∨ (p5 ∨ p5)) ∨ (p1 → (True ∨ False))) ∨ p5) ∨ (p5 ∨ p2))) ∨ (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655417909708479565330209517081 : ((((((p5 ∨ (((p3 ∨ p3) ∨ p1) ∨ p2)) → ((p3 ∧ ((True ∧ ((True ∨ True) ∧ p3)) ∨ p1)) ∧ False)) ∨ (p2 → p5)) ∨ (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159896430830538362533133763447 : ((((((((p2 ∨ p5) → p4) ∧ p2) ∧ ((True ∧ True) → (p5 → p5))) → (p4 → p3)) ∨ True) → p3) → (p3 ∨ ((p1 ∧ p1) → (p2 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325018009211680643091438391574 : (p5 ∨ ((p2 ∧ True) → (((p4 ∧ (p2 ∧ True)) ∧ ((p1 ∨ ((p3 → False) ∧ True)) → ((p2 ∨ p5) → (p5 ∨ (p4 → False))))) ∨ (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_158515190759869637535568071461 : (((p2 ∨ p1) → ((p3 ∧ (p5 ∨ ((p3 → ((((p5 → p4) ∧ p1) ∧ p1) ∨ p5)) ∨ p5))) ∨ True)) ∨ (p2 ∨ ((False ∨ (True → False)) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_683157479775919834737388952209 : ((((p4 ∧ ((p3 ∧ (True ∨ ((p2 → p3) ∨ (((p2 → (p5 → p1)) → p3) ∧ True)))) → p5)) ∧ ((True ∨ ((p1 → p2) → p4)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324251846908808751296663018126 : (p5 ∨ (((p5 ∧ (p4 ∧ (p5 ∧ (p4 ∨ p2)))) ∧ p5) ∨ ((False ∧ (True ∧ (((p4 → ((True ∧ p4) ∨ False)) ∧ (p1 ∨ True)) ∨ p2))) → False))) := by
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
theorem thm_5_vars_136516339116664198737414175618 : (((False ∨ (p5 ∧ p3)) ∧ (p5 ∨ (((False ∧ ((p5 ∧ (False → False)) ∧ (True ∨ (p2 ∨ p2)))) ∨ p3) → (p1 ∨ True)))) ∨ (p5 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207335821236569996836246500917 : ((((True ∨ True) ∨ (p5 → p2)) ∨ p2) → (((((p3 ∨ p1) ∧ False) ∨ p4) ∨ ((True ∨ ((p1 ∧ (p5 ∧ (p1 ∧ True))) ∨ p1)) → p5)) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48103026418474761681905120563 : (((((p2 → (False → p5)) ∨ True) ∨ ((((p5 → p5) ∧ (False → p3)) ∨ (((True → (p4 ∧ False)) ∨ p3) → p2)) ∨ p5)) → (p3 ∨ True)) ∨ False) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135443076077736601781308489177 : ((((((True → p5) ∧ (((p4 → p1) ∨ p1) ∧ (p5 ∨ (True ∧ False)))) ∨ (p3 ∧ p5)) ∧ p1) → ((True → p4) ∨ p5)) ∨ ((p2 → p4) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113436840346009238750548003654 : (((((p2 ∨ (p5 ∨ ((((((p2 ∧ (p5 ∨ p5)) ∧ p5) → p3) ∨ p2) ∨ p5) → p2))) → (True ∧ p5)) ∨ p4) ∨ (p1 ∨ True)) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152526298342740738567738013091 : (((p4 → (p1 ∧ p1)) ∨ ((p3 ∨ False) ∧ (((p2 ∧ (p1 → (p3 ∨ ((True → False) ∧ p2)))) ∧ p3) ∨ True))) → (((p4 → True) → p2) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158131448940276609718322523954 : (((((p4 ∧ p3) ∨ p1) ∨ p5) ∨ (p2 ∨ (True ∨ (((True ∨ p5) ∨ False) → (p3 ∨ (p1 ∧ p1)))))) ∨ ((((True ∧ True) ∧ p2) ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55685092971645994891278159069 : (((((p3 ∨ True) ∨ p4) ∨ p4) ∧ ((((p2 → True) ∧ p5) → p3) → ((p4 ∨ ((((p3 → p4) ∧ True) ∨ p3) ∧ True)) → (p5 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759267292945893165098260339688 : (((p2 ∧ (((p1 → ((p4 ∧ p1) ∧ (((p5 → (False → False)) ∧ False) ∧ True))) ∨ ((p2 → False) ∧ ((p2 ∧ p2) ∧ False))) → (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208958165917794436235359547250 : ((True ∨ ((p4 ∧ (p1 ∧ p2)) → p1)) → (((p2 ∨ p5) → ((False ∧ (p2 ∧ (p3 → (False ∨ p3)))) ∨ (p3 ∨ p1))) ∨ ((p1 ∧ False) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188723225745530995320704567672 : ((((p4 → ((p1 ∧ p3) ∨ p4)) → p2) → (p2 → True)) ∧ ((p3 ∧ (((p1 ∨ (p3 ∨ p5)) → ((p1 ∧ True) → p4)) ∧ p1)) ∨ (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206962228536261176849363235045 : ((((p3 ∧ (p5 ∧ p2)) → True) ∧ p2) → (((p4 ∧ p3) ∨ ((p4 ∨ p4) ∨ ((p1 ∨ (p1 → (True ∧ (False → True)))) ∨ p3))) ∨ (p4 ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686940251808466107719976604049 : ((((p2 ∨ (((p3 → (True ∨ ((p2 → p2) ∨ (p4 ∧ (p3 → (p2 ∨ p5)))))) ∨ p1) ∧ p4)) → ((p4 → p5) ∨ (p5 → (False → p1)))) ∨ p1) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655865590274676360419664768476 : ((((((p2 ∨ (p1 ∨ p5)) ∧ (False ∨ (p5 ∨ ((p4 ∧ (p5 ∨ (False ∧ p3))) → (True ∧ p3))))) → ((p1 → True) ∧ p2)) ∨ (p1 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_55049184932446448091469849350 : (((True ∨ (p5 → ((p1 ∧ p2) ∨ p4))) ∧ ((((p5 ∨ p3) ∨ p1) ∧ ((False → p5) → p4)) ∨ ((((p1 ∨ p5) ∨ False) ∧ p4) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656391645761171908784694462776 : ((((((p1 → ((((p3 ∧ p4) → p5) ∧ True) → p3)) ∧ p3) ∧ ((p5 → (True ∧ p4)) ∧ ((False → (p5 ∧ False)) → p5))) ∨ (p3 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_254047402405046410419275195840 : ((p2 ∧ True) → ((p5 → (p1 ∨ (((p2 → (((p4 → True) → p3) ∧ (False ∨ p2))) ∧ False) → p3))) → ((p3 → (p2 → (p3 ∨ p4))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117382833722076935554398463630 : ((p1 ∧ (((p4 ∧ (((((p2 ∧ (p4 ∧ p5)) ∨ p1) ∧ p3) ∧ p3) → (False → ((False ∧ True) ∨ p5)))) ∧ (p1 ∧ False)) ∧ p5)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329772026072173944428789686129 : (True → (True ∧ (((p2 ∧ ((((p4 → (p1 ∧ False)) ∧ p3) ∨ True) ∧ p5)) ∨ False) → ((False ∨ (((p2 ∧ False) ∧ p1) ∨ (p1 ∨ True))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114495994160021445743386306307 : ((((p3 → ((((False → p3) ∨ False) → p1) ∨ p5)) → ((True ∧ (p4 ∧ (p5 → p3))) → p5)) → (True ∧ (True → (p4 ∨ p2)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173118579825181855940755876863 : ((p2 ∨ (((p4 ∧ ((p3 ∨ p1) ∧ p3)) ∧ p2) ∨ (False → (p5 → (p2 ∧ p5))))) ∨ ((False → (((p4 → (p2 → p2)) → p1) ∧ p4)) ∨ p1)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602577849273001442569348800145 : ((((False ∨ ((False ∧ (((((True ∨ p2) ∧ p5) → ((p3 ∨ False) ∨ (p5 ∧ True))) ∨ ((p5 ∨ True) ∧ (False ∧ p1))) ∨ p2)) ∨ False)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351712722376765919964455732780 : (p4 → ((p2 ∨ ((p2 ∨ False) ∨ (((False ∧ (p5 ∨ p5)) → (p2 → p1)) ∨ p2))) ∧ ((((p1 ∧ p2) → (False ∨ False)) ∨ (False → p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258801241656643692976092487902 : ((True → False) → (True ∧ (p3 → ((p4 ∨ (p2 ∧ (p2 ∧ p5))) → (p4 → (((p1 ∨ p2) ∧ (False ∧ ((p1 ∨ p5) → (p3 ∨ True)))) ∨ p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166892037783436219971589650573 : ((((((False → (False ∨ (p2 → p4))) → True) → (p4 ∨ True)) → ((p1 ∨ True) → p4)) ∧ p2) → ((True ∧ (((p2 ∨ p2) ∧ p3) ∨ p3)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : (((False → (False ∨ (p2 → p4))) → True) → (p4 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h13 := h9 h11
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h19 : (((False → (False ∨ (p2 → p4))) → True) → (p4 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h21 := h17 h19
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h27 : (((False → (False ∨ (p2 → p4))) → True) → (p4 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h28
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h29 := h25 h27
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h30 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h31 := h29 h30
    -- One of the premise coincides with the conclusion.
    exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310502824957735029096909619180 : (p2 ∨ (((False ∧ True) ∨ ((False ∨ p1) ∨ p4)) ∨ (p2 → ((p5 ∨ ((p4 ∨ (True ∨ (p3 ∨ p4))) ∨ p4)) ∨ (p3 → ((p1 → p1) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197586989607888903260948533645 : (((p3 ∧ ((p1 → p3) ∨ p2)) ∨ (p4 ∧ p5)) ∨ (p2 ∨ (((p4 ∨ ((((p3 → (p5 ∨ (p2 ∧ p3))) → p5) → p4) ∨ True)) ∨ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_589967302072243328214567942286 : ((((((((((p3 ∧ (False ∧ (p1 ∨ p5))) ∨ p1) ∧ p5) → ((p3 ∨ p1) ∨ False)) ∨ False) → (p1 ∨ (p5 → (True ∧ p3)))) → p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167522073062370685508180967257 : ((((p3 ∧ p1) → (p3 ∧ ((p1 ∧ ((p4 ∨ True) → (p5 ∧ p3))) → True))) ∧ (p2 ∨ False)) → ((((True → (p1 ∨ False)) ∨ True) ∧ p5) → p5)) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250704667337499647563485332320 : ((p1 → False) ∨ ((((p4 ∨ False) ∧ (p1 → (((True ∨ p3) ∧ ((p4 → p4) → p5)) ∧ p5))) ∨ (p5 ∨ p4)) ∨ (False ∨ (p1 ∨ (False → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196815061247735650336952959778 : (((True ∧ ((p3 ∨ p3) ∧ (p1 ∧ p1))) ∧ p3) ∨ (p2 → (p1 → ((((p1 ∧ p3) ∧ (p1 → ((False → p4) ∧ p3))) → p1) ∨ (p4 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343257234233537552898786148447 : (p2 → ((True ∧ True) ∧ (((p4 ∧ ((p3 ∨ (((p3 → p1) ∧ (p2 ∧ p1)) ∨ (False → p3))) → p5)) ∨ p1) ∨ (False → (p5 ∨ (p3 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764597403810282843345605747995 : (((p4 ∧ (((p2 ∧ (((True ∧ p2) ∧ True) ∨ ((((p4 ∧ (p3 → p4)) ∨ p4) ∨ p1) → p1))) → (p3 ∨ ((p3 → p5) ∨ p1))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694994461874270309723789297459 : ((((((p4 ∧ (p4 ∨ ((p1 ∨ True) ∨ p1))) ∨ (p5 ∨ (False → p1))) ∧ p1) → ((((p1 → ((p4 ∨ p1) ∧ p5)) ∨ False) ∧ p4) → p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h12 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h13 := h5 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h18 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h19 := h5 h18
            -- We need to get the right conjuct of h19 based on <expert-advice>.
            let h20 := h19.right
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h22 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h23 := h5 h22
            -- We need to get the right conjuct of h23 based on <expert-advice>.
            let h24 := h23.right
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h25 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h26 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h27 := h5 h26
          -- We need to get the right conjuct of h27 based on <expert-advice>.
          let h28 := h27.right
          -- One of the premise coincides with the conclusion.
          exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h32 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h33 := h5 h32
        -- We need to get the right conjuct of h33 based on <expert-advice>.
        let h34 := h33.right
        -- One of the premise coincides with the conclusion.
        exact h34
  case inr h35 =>
    -- False on the left can always be used.
    apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208008576499987543878068456120 : ((((p3 ∧ True) → p4) ∨ (True → p3)) → (((p5 → False) ∨ ((p5 → (True ∧ p5)) ∧ (p4 → True))) ∨ (((p4 ∨ False) ∨ (p5 ∨ p3)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653584741138585619830446887635 : ((((((((((True ∧ p4) ∧ p5) ∧ False) → ((p4 → (False ∧ p4)) ∧ p1)) → (p1 → ((p3 → False) → p1))) ∧ True) ∧ True) ∨ (p3 ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354692090408475017309784619148 : (p5 → ((((p4 ∨ ((True → p1) ∧ (((False → p2) ∨ p5) ∧ p4))) ∧ (p1 ∨ (((p4 → p2) ∧ (True ∨ p3)) → p4))) ∨ (p1 → p5)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617432865823355687400117312980 : (((((p3 → ((p2 ∨ (True → p1)) ∨ (p5 ∨ p4))) → (p5 ∧ ((p5 ∨ ((True ∧ p2) → ((p1 ∨ p1) ∨ True))) ∧ (p5 ∧ p5)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217018451503437759790606414029 : ((((p3 ∧ p1) ∧ p5) ∨ True) → (p3 → (((p4 ∨ (p2 → p1)) ∨ (((p2 → p1) → p5) ∨ (((p4 ∧ (p4 ∨ p2)) ∧ p4) ∨ p3))) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806667412041921589790419316486 : (((p4 → ((False → (((True ∧ ((p2 → False) ∧ ((p1 ∧ p3) ∧ ((((False ∨ p4) → p2) ∨ True) ∨ p5)))) ∨ (True ∨ True)) ∧ p2)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137178652235882199080309811653 : ((False ∧ (((True → p2) ∧ (((p3 ∧ p1) ∨ (True ∧ True)) ∨ True)) ∧ (p1 ∨ ((p3 → ((p1 ∧ p1) ∧ True)) ∧ p4)))) ∨ ((False ∧ p5) → p5)) := by
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
theorem thm_5_vars_350147923843293649060287118889 : (p4 → (((((p2 ∨ (((p4 → False) ∧ p1) ∧ p3)) → True) → False) ∧ (((p3 → p4) ∨ p4) → (p1 → (False ∨ (p2 ∧ (p4 → True)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54573265852481955378364645777 : (((False ∨ ((p3 ∨ p3) ∧ (True → (p1 ∨ False)))) ∨ (((p4 ∨ (p5 → p1)) → (p2 → ((p5 ∧ p3) ∨ ((p2 ∨ p4) ∧ p2)))) ∨ p1)) ∨ p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84151387557506655967497939548 : (((p5 ∧ (True → ((True ∨ (p4 ∨ (p4 → (((p5 → p1) ∨ p2) ∨ p1)))) ∧ p3))) ∧ (((p1 ∨ p3) → p3) → (p4 ∧ (False ∧ p1)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 ∨ p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h6
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113574294314362852072017064837 : (((True ∧ ((((p4 ∨ ((False → (p4 → p5)) ∨ (True ∨ False))) ∨ False) → (p2 ∨ p1)) ∧ ((p4 ∨ p1) ∨ False))) ∨ (p1 ∨ True)) ∨ (p1 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149627779882095454936573247294 : ((p4 ∧ ((((p2 ∨ p1) → p4) → (((p1 ∧ (True ∨ p5)) ∧ True) ∧ ((p3 ∨ p2) ∨ (p4 → p2)))) ∧ False)) ∨ (((False ∨ p3) → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356241166809529049113929501475 : (p5 → ((p3 ∨ (p1 → ((((p1 ∧ p2) → p1) → (p3 ∨ p2)) ∨ ((False ∨ False) → p2)))) ∧ ((p4 ∨ (p4 ∨ p5)) ∧ ((p5 → p4) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197425167947455586850980293200 : (((p4 → (p3 → ((p2 → True) → p2))) → p3) ∨ ((p1 ∧ True) ∨ ((p3 ∨ ((p5 → (p4 ∨ (False → p4))) ∨ ((p2 ∧ True) → p1))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113668039581961550805459998952 : (((((((p3 ∧ p3) ∨ (p3 → (p1 ∧ (p3 → p4)))) ∧ ((False ∨ p4) ∧ (p1 → False))) → (True ∧ p5)) ∨ p5) → (p1 ∨ False)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57763382833407385528573957441 : ((((p4 → p2) → p4) → ((True ∧ (p5 ∧ (p5 → (p1 ∧ ((p3 ∧ (p3 ∨ p1)) ∧ False))))) → (p1 → ((p1 → p5) → (p1 ∧ False))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200506552768665991929220695398 : (((p5 ∧ p5) → (((p5 → p5) ∧ False) ∧ p4)) → (((((p2 → (False → p4)) → (p4 ∧ False)) ∨ p2) → False) ∨ (p5 → (p1 ∨ (False ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253921370098541765829054982426 : ((p1 ∧ p4) → ((False ∧ (p3 ∨ ((p5 ∧ False) ∧ (((p1 ∧ False) ∨ False) ∧ (((True ∨ p2) → (True → False)) ∨ False))))) ∨ (p2 ∨ (p4 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471469336443685440629220883179 : (((((((p2 ∨ (p5 ∧ (p4 → (p2 ∨ False)))) ∨ p5) ∨ True) ∨ True) ∨ (((p3 ∨ (p1 ∨ True)) ∧ (((p3 → False) ∨ p2) → p3)) → p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737903542727761332025468325100 : ((((True ∧ p2) ∨ (p3 ∨ (((True ∧ p3) ∧ p4) ∨ (((p3 ∨ True) ∧ (((True ∨ p5) → p4) ∨ ((p3 → False) ∧ p5))) ∨ (False → p1))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198333556885013794136886981541 : ((p2 ∧ (((p3 ∨ p1) ∨ (p1 ∧ p4)) ∨ p1)) ∨ (((True → ((p4 → True) → p3)) ∧ p2) ∨ (False → (p5 ∨ (p2 ∨ ((p5 → p2) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349251439665073759614298942871 : (p3 → (p1 → (p1 ∧ (((False ∨ (((((p5 → ((False ∧ p4) → (False ∨ True))) ∧ ((p5 ∨ p2) ∧ True)) ∧ p4) ∨ p3) ∧ p1)) → False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64100050846306266458462652458 : ((False ∨ (((((((p4 ∧ p2) → p5) ∧ p3) → p5) ∧ p5) → p4) → (((p3 ∨ p5) ∨ (p5 ∨ True)) ∨ ((False ∨ (True → p5)) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232356087450318057948253747972 : (((p4 → p3) → p1) → (False ∨ (((True → p4) ∧ ((p5 ∧ (p2 ∨ p1)) ∧ p5)) → (p4 ∧ (((p3 ∧ p2) ∨ True) → ((p3 ∨ p5) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h2.left
    let h20 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h26 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h2.left
    let h29 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h31
    case inr h35 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662852028169969998658576338977 : (((((p5 ∧ (p4 ∨ p3)) ∧ ((((p2 ∨ True) ∨ (True → p4)) ∨ ((((p1 → p3) ∨ p5) ∨ p1) ∧ p3)) ∧ (p2 ∨ p5))) → (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619843060749202362595208710402 : (((((p3 ∨ p4) ∧ ((p5 → p5) → (((((False ∧ p5) → (p1 ∨ p5)) ∧ p3) ∨ (((p1 ∨ (p2 ∨ p4)) ∨ p4) ∧ p3)) ∨ p1))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_158261909380641745539123748632 : (((p1 ∧ (False ∧ p3)) ∨ ((p3 ∨ (((True ∨ (False ∧ p1)) ∨ p4) → p1)) ∨ ((p1 → p2) ∨ False))) ∨ ((p4 → ((p1 ∧ True) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49928995486843332880900339145 : ((((p5 ∧ (p3 ∧ (((False → ((p3 ∧ (((p2 ∨ p1) ∨ False) → False)) ∨ True)) ∨ p1) ∨ p2))) → p1) ∧ (p5 ∧ ((False → p2) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



