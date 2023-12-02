variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319914749570257115558381713728 : (p4 ∨ (((p2 → (p5 ∨ p3)) → False) → ((((True ∨ (False ∧ (p1 ∨ ((False → (True ∨ (p5 ∨ p5))) ∧ (p4 → False))))) → p4) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158194267634304700134960257573 : ((((p2 ∧ p5) ∧ p2) ∧ (((((p3 ∧ p1) ∧ p3) → True) ∧ p3) ∨ (False ∨ (p2 ∨ (p1 → p5))))) ∨ ((p3 → p3) ∨ (p3 → (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43579160619508587079181599214 : (((((((((((p4 → p1) → p5) ∨ True) ∨ ((False → True) ∨ p1)) ∨ ((p4 ∧ True) ∧ (False → p2))) ∧ p5) → p2) ∨ True) → False) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317609515288369362104602344460 : (p4 ∨ (((True → (p5 → (p2 ∨ (p3 → (p4 ∨ ((((p3 → (False ∧ p2)) → (False → p1)) ∧ (p1 → p2)) ∨ (True ∨ p1))))))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324401404365688290218423044200 : (p5 ∨ (((p4 ∨ ((p2 ∧ p4) → p2)) → False) → (((((((((p1 ∧ (True → p1)) → p3) ∨ p4) ∨ p2) → p4) → p1) ∧ p1) → p5) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ ((p2 ∧ p4) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h5
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (p4 ∨ ((p2 ∧ p4) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h10
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135163827676297228233027126536 : (((((p2 → ((((p2 ∧ p2) ∧ (p4 ∨ ((False ∨ (True ∨ False)) ∧ p3))) ∧ p5) ∨ p2)) → p4) ∧ True) → (p5 ∨ p4)) ∨ (p2 → (p3 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → ((((p2 ∧ p2) ∧ (p4 ∨ ((False ∨ (True ∨ False)) ∧ p3))) ∧ p5) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337958702553448687590844439533 : (p1 → ((p1 ∧ (p1 ∧ (p3 → (((True → (p5 → p5)) ∨ p2) → False)))) ∨ ((((p1 ∨ p5) ∨ (p5 → p3)) ∧ p3) ∨ (p1 ∨ (p1 → p1))))) := by
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
theorem thm_5_vars_318853896047691555125225430287 : (p4 ∨ (((((p2 → p3) ∨ False) ∨ ((p2 ∨ (p1 ∧ p4)) → (False ∨ ((p2 ∨ (p3 ∨ p1)) ∨ (True ∨ p5))))) ∨ False) ∨ (False ∧ (p1 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179697217227802659034814956709 : (((((p3 ∧ ((p2 ∧ (True ∧ p2)) ∧ (p5 ∧ True))) ∨ True) ∨ p2) ∧ p2) → (((((p2 ∨ p1) ∨ p4) → (p2 ∨ p5)) → p5) ∨ (False → False))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h9.left
      let h15 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148531632722148441461828341359 : ((((p4 → False) ∧ ((p1 → ((False ∧ p5) ∧ p4)) ∨ (p4 → p1))) → ((p3 ∧ (p4 ∨ (True ∧ p2))) → p5)) ∨ (True → (True ∨ (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150145639303005988110101591275 : ((p1 → (((True → (True ∨ ((False → (p3 → p2)) ∨ p1))) → (p2 ∨ (False ∨ ((p5 ∨ p4) ∧ p5)))) ∨ p1)) ∨ (((p5 ∧ p4) ∨ p4) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49808130467223407698858026140 : (((False → (((p1 ∨ p1) ∧ True) → ((((True → ((p1 → True) ∧ p3)) ∨ False) → (False ∨ (p3 → p2))) → p5))) → ((False ∨ p5) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158591284477260413599531572610 : ((False ∧ ((((p5 → (p4 ∨ (True ∧ (p1 → p2)))) ∧ ((p1 → p1) → (p2 → p5))) ∧ False) ∧ p4)) ∨ ((((True ∧ p4) ∧ p3) → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303881230056411801536826337252 : (p1 ∨ ((((p5 → (False ∧ p3)) → ((((((False → True) ∨ (p4 ∧ p5)) → p3) → p1) → p5) → p3)) ∨ (p1 → (False → (p5 ∨ p2)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47230714138083165422538001854 : (((((p1 ∧ (False ∨ (p3 → (False → p3)))) ∨ p1) ∨ (((False ∨ p3) ∨ (((False → (p3 ∨ p2)) ∧ True) → p5)) ∨ True)) ∨ (p5 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782534388217603387586706506083 : (((p3 ∨ ((False ∧ (((False ∨ (False → ((((p2 → (p4 → p2)) → (p3 ∨ (p2 ∨ (p3 → p2)))) ∧ p2) ∨ p4))) → p2) ∧ False)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111063859289552778369639431070 : ((((True → ((((p4 ∨ (p5 ∨ p1)) → True) ∧ p5) → (True ∧ (p2 ∧ False)))) ∧ ((True ∨ p4) ∨ ((p5 ∧ p5) ∧ False))) ∧ False) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136445956948622547577175808423 : (((p2 ∧ ((True ∧ p3) → p2)) → ((True → False) ∨ (False ∨ ((p1 → ((p4 ∧ p3) ∨ (True → (p3 → True)))) ∨ True)))) ∨ ((p3 → p4) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710822092206179183333325515853 : (((((p4 ∧ p5) ∧ (False ∧ (p1 → True))) ∧ ((((False ∨ (p3 ∧ (p4 ∧ (p3 → False)))) → False) ∨ (p1 ∧ (True ∨ (True ∧ p3)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712609917508504832421467444848 : (((((p3 ∨ (p3 → True)) → (p1 ∧ False)) ∨ (False → (p3 ∨ (p5 ∨ ((False → (((p2 ∨ ((False ∨ p5) ∧ False)) → p3) ∧ p1)) → False))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_591331006518333482204553238853 : ((((((p5 ∨ ((True ∨ (False ∨ p3)) ∨ ((True ∧ True) ∧ p4))) ∧ ((((False ∨ p4) ∨ True) ∨ (p1 → p2)) → False)) ∧ (False ∧ False)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221311487012328786535494132115 : (((p4 ∨ True) ∨ False) ∧ (p1 ∨ ((((p4 ∨ ((True → (p4 ∧ (p3 ∨ p3))) ∨ p2)) ∨ ((True ∨ (p1 ∧ p1)) ∧ True)) ∨ p2) ∨ (p5 → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639021049197696316723102555766 : (((((((True → p3) ∧ p2) ∧ p3) ∨ (((False ∧ ((p4 → p2) ∧ p5)) → (p1 → (((p4 ∧ (p3 ∧ p5)) → p5) ∧ False))) ∨ p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314423965007686273898878890051 : (p3 ∨ (((((p4 ∧ (p1 → p4)) ∨ True) ∨ p2) ∧ ((True → p4) ∨ ((p3 → ((p4 ∧ p3) ∨ p4)) → p1))) ∨ (((p2 ∨ False) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234495124230159512259525944175 : ((p2 → (p5 ∨ p4)) → ((False ∨ (p4 → p5)) → (((p5 → (False ∧ True)) → (((p5 ∨ (True → p2)) → p5) ∧ (p5 ∨ p3))) ∨ (p5 → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52814903575245386779095203061 : ((((((p2 ∨ True) ∧ p4) ∨ p3) ∧ (((p3 → False) ∨ False) ∧ (p1 → p3))) → ((p5 → (False ∨ p4)) ∨ ((p3 ∧ (p4 → p3)) → p1))) ∨ False) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h3.left
      let h15 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40764826141932535819583927853 : (((((p1 ∧ p4) → (((False ∨ p4) ∧ p2) ∧ (((p3 ∨ (True ∧ ((p3 ∧ p3) ∨ p2))) ∨ (p2 → (p1 ∧ p3))) → p5))) → False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783592350448437507431872888771 : (((p3 ∨ ((((p5 → p5) ∧ (p5 ∨ (True → (True → p3)))) → False) → ((p4 ∧ (p3 ∧ (p4 ∨ p4))) ∨ ((True ∧ (True → p4)) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54696396420917775386322227236 : ((((((True ∧ p1) ∧ p3) → False) ∧ (True ∧ p3)) → ((p4 → ((p3 ∧ (p5 ∧ p1)) ∨ ((p2 → ((p4 ∧ p1) → True)) → p4))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352832212064576956398856043250 : (p4 → ((p1 → p2) → (False ∨ ((p1 → ((p3 ∧ p3) ∧ ((True ∧ (True ∨ (p5 → ((p4 ∧ (p4 ∨ p2)) → p3)))) → False))) ∨ (p1 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255168367729770078323541612229 : ((p4 ∧ p3) → (True → (((p4 ∧ (p5 ∧ (p5 ∨ False))) ∧ False) ∨ ((p1 → (((p2 ∨ ((p3 → (p4 → p3)) → p3)) ∨ p5) ∧ True)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184852741972783747668678467128 : ((((p2 ∧ p4) ∧ p1) ∧ (((p4 ∨ p3) ∧ True) → (p4 ∨ p5))) ∨ (False → (p5 → (p3 ∨ (((p2 ∧ True) → (p1 ∧ p1)) ∨ (True ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174443705478442962316295149552 : (((((p2 ∨ p2) ∧ (p4 ∧ p3)) ∨ (True ∨ p5)) → (((True → True) ∧ False) ∧ p2)) → (((p4 → True) → p5) → (p4 → (p1 ∧ (p2 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∨ p2) ∧ (p4 ∧ p3)) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (((p2 ∨ p2) ∧ (p4 ∧ p3)) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (((p2 ∨ p2) ∧ (p4 ∧ p3)) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230658589089962638134336369370 : (((p3 → p2) ∧ p2) → ((p5 ∨ p4) ∨ (((p2 → p3) ∧ (p4 → True)) → (((((True ∨ (True → False)) ∧ p2) ∨ p2) ∨ p4) ∨ (p1 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695326602995770858306775431228 : (((((True ∧ (False ∧ (False ∧ ((p2 ∨ ((p2 ∧ p1) ∧ False)) → p2)))) → p3) → ((p2 ∧ (False → ((p5 ∨ p5) ∨ (p2 ∨ True)))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58448011944423717191141766214 : (((p3 ∨ p1) ∧ ((False → (p5 ∧ p3)) → (p4 ∧ ((((p2 → p1) ∧ (p1 ∧ p3)) ∧ p3) ∨ ((p5 → (p3 ∨ p5)) ∧ (True → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156718310796287357601082043022 : ((((False ∧ (p2 → (((p3 ∧ p3) → p1) ∨ p3))) ∨ ((p2 → p5) ∨ ((p1 → p3) ∧ p4))) ∧ p4) ∨ ((False → False) ∧ ((p2 ∧ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689129491100413187648701547558 : (((((((p2 → p2) ∧ ((p5 ∨ p4) → ((p2 ∧ (p2 ∨ p1)) ∧ p1))) ∧ True) → p4) ∨ (((False ∧ p5) ∧ (p4 ∨ p5)) → (p4 → p2))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110883170799518826810477407744 : (((((((False ∧ p2) ∧ p5) ∨ (p1 ∧ ((((p3 → p5) ∨ p1) → p1) ∧ True))) ∨ (p1 ∨ ((p5 → True) ∧ p1))) → p5) ∧ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141827545520763515441155652651 : (((True ∨ p4) ∨ (p1 ∧ ((True → ((False ∨ False) → (False ∧ (p5 → ((True → p2) ∧ p3))))) → (False ∨ (p2 ∨ True))))) → (p3 → (p2 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190400759019918604572927798221 : (((p3 ∧ ((p1 ∧ p2) ∨ ((p3 ∧ p2) ∨ True))) ∨ True) ∨ (((p5 → (((p1 → p4) ∧ True) → (p5 ∧ (p5 → (p1 ∨ p3))))) ∧ False) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807542925264437132103011066857 : (((p4 → ((((p1 → p4) → False) → (p5 → p2)) → (((p1 ∨ (p3 ∨ ((p1 ∨ p2) ∧ ((p3 ∧ False) ∧ p5)))) ∧ p2) → (p5 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260949364119431635710847855106 : ((p4 → p1) → ((((True → False) ∧ ((((True → (p1 → (p5 ∨ ((p5 ∨ (True → p1)) ∧ p2)))) → p4) → p4) ∨ (p4 ∨ True))) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345410971640770651547792679249 : (p3 → (((((False ∧ p2) → (p1 ∨ (p4 ∨ (p2 ∧ False)))) ∨ (p1 ∧ (p1 ∨ ((((p4 ∧ p5) ∧ (p4 ∨ p5)) ∧ True) ∨ p3)))) → p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137885999553220470532832408278 : ((p4 ∨ ((p2 ∨ (p5 ∧ (p1 ∧ ((p4 ∧ (p2 → (p4 ∧ False))) → (False → (p2 → ((p4 ∧ p3) → True))))))) ∨ p3)) ∨ ((p3 ∧ False) → False)) := by
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
theorem thm_5_vars_913896221254828147643788152952 : (((((p3 → ((p3 ∨ (((True ∨ (p2 → (p2 ∨ p5))) ∧ True) ∧ p2)) ∧ False)) ∧ p3) ∧ (False ∨ ((p1 → p3) ∧ (p5 → (p4 ∨ p3))))) → p4) ∧ True) := by
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
  cases h3
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113857551030999470127660769794 : (((p2 → (((p4 ∨ ((((p4 ∧ (True → (p1 → ((p1 ∨ False) → p5)))) → p4) ∧ True) ∧ p4)) ∧ p4) ∧ p3)) → (p4 ∨ p5)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184376328510394127073141555756 : (((True → ((p5 ∨ ((p3 ∧ (p3 ∨ p1)) ∧ True)) ∨ p5)) → False) ∨ ((p4 ∨ False) → (((p3 ∨ True) → False) → (p5 ∨ (p3 → (True ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645665337137515414350292379942 : ((((p5 ∨ ((((p2 → (((p3 → (p3 ∨ False)) ∧ p1) ∧ (True → ((False ∧ p3) → p4)))) → p2) ∧ (p5 → p4)) → (p2 ∨ False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130483220003898313762959667008 : ((((((p2 ∨ (p1 ∨ (False ∧ ((p5 ∧ False) ∨ p3)))) ∨ (True ∨ p1)) ∧ (p4 ∨ p3)) ∧ p3) → ((True ∧ p5) ∨ p3)) ∧ ((False ∧ False) → p5)) := by
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
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  -- Implications on the right can always be decomposed.
  intro h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310140314873194003607197008418 : (p2 ∨ ((((p4 ∨ ((p1 → (p5 ∨ ((False ∨ True) ∧ p3))) ∨ p3)) ∨ True) ∧ p1) → ((((p1 → p4) ∧ (p4 ∨ (p5 ∧ p1))) ∨ p1) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341065198347622288131865152449 : (p2 → ((p4 ∨ (((p1 → p1) ∧ (False ∨ (((p1 → (p4 ∧ p1)) ∨ False) ∨ (p5 → (False ∨ (p4 ∨ False)))))) ∨ ((True ∨ p5) → p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672981599036636048313481235846 : (((((((p4 → (True ∨ (False → (p2 ∨ (True ∨ (p5 ∨ p1)))))) ∨ p5) ∧ p3) ∨ ((p5 → (p2 → False)) ∨ p2)) → ((p5 ∨ p2) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51876636165112072002800774158 : ((((p4 ∨ ((False ∨ (False ∨ (p4 ∨ ((p4 ∨ (True ∨ p1)) ∧ p5)))) ∧ False)) ∨ p5) ∨ ((p1 ∨ ((p4 → True) ∧ p2)) ∨ (p3 → True))) ∨ p5) := by
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
theorem thm_5_vars_327119344807587449457724978853 : (True → (((True ∨ p2) → ((p4 ∧ (True ∧ p5)) → (p4 → ((p5 → (p1 ∨ False)) ∨ (p5 ∧ ((p2 ∧ p2) ∧ (True → (p4 ∨ p3)))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114497279131589524520627881096 : ((((((p1 → (p5 ∨ p3)) ∧ p1) ∨ p1) ∨ (((p4 → (p1 ∨ p5)) → (p2 ∧ p5)) ∨ p4)) → ((p5 ∨ False) ∨ (p3 → True))) ∨ (p5 ∧ p2)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157341714224885408100234007625 : (((p3 ∨ ((((p1 → ((p2 ∧ p4) ∨ p5)) → True) ∧ (p3 ∨ p1)) ∧ ((p1 ∧ True) ∨ p5))) → False) ∨ ((p3 → (p5 → False)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713076141349118198097229226212 : ((((p4 ∧ (p3 → (True → (p1 ∨ p1)))) ∨ (p5 ∨ ((p5 → (True ∧ (((p4 ∧ (False ∧ p1)) ∧ ((p3 → p2) → True)) → False))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312373917448834617186096415813 : (p2 ∨ (p3 → (((p5 ∨ (((p5 ∨ p1) ∧ p1) → p2)) ∨ (p5 ∨ False)) ∨ (p5 → (((p5 → False) → p2) ∨ ((p5 → p2) → (True ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732091998446889272154562575857 : ((((True ∧ p2) ∧ (((False ∧ (False ∧ (((True ∧ (True → (True → p3))) ∧ False) ∨ p5))) → ((p2 → (p4 → (p5 ∧ p4))) ∧ p5)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606343786594595419443372038901 : (((((((p2 ∨ (p2 → (((p4 ∧ (p1 ∧ p2)) → (p4 → (p2 ∧ (((p3 → False) ∨ p4) → True)))) → True))) → p1) ∨ p5) ∧ p2) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_2322433775185045151916171347 : ((p4 ∧ (((False → ((False → (False ∨ p1)) → p4)) ∨ (p1 ∧ p1)) → p4)) → (((p2 ∨ (p1 ∨ p5)) ∧ ((False ∧ p1) ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_118210821508986367869289110298 : ((p1 ∨ (((False ∧ ((p1 → (p3 → ((p3 → False) ∨ p2))) ∨ ((p2 ∧ p1) → True))) ∨ (p4 ∧ ((True → p2) ∨ p1))) ∧ True)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56586302199447873316129011598 : (((p1 → (p4 → (False ∧ False))) → ((p4 ∧ p5) ∧ ((False ∨ (((p3 ∨ (p1 → (False → False))) → p2) ∧ ((p2 ∨ p3) ∧ p1))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317117183505387455260063840020 : (p3 ∨ (p5 → (((p5 → ((p4 ∧ p3) ∨ p5)) ∧ (((False ∧ p5) ∨ False) ∨ True)) ∨ ((False ∧ (p1 ∧ p2)) ∨ (p4 ∧ (p1 ∧ (p2 → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244814200903578428742701627396 : ((p1 ∧ p1) ∨ ((False ∨ ((p4 → (((p4 ∨ p2) ∨ p3) ∧ False)) → (p1 → (p4 ∨ (p2 → (True ∧ p5)))))) ∨ (p2 ∨ ((p3 ∨ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_319487565430537565780608047089 : (p4 ∨ (((((p1 ∧ (p4 ∧ p2)) ∧ p4) ∨ p5) → ((False → p3) → False)) → (p3 → ((((True ∨ p5) ∧ p3) ∨ p4) ∨ (p5 ∨ (p2 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127076396018365544879653300166 : ((False ∨ ((p3 ∧ ((p3 → True) ∨ ((p5 → p5) ∨ True))) ∧ ((True ∨ ((False → p3) ∧ ((False ∧ p2) → (p3 → p4)))) → p5))) → (p5 ∨ p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : (True ∨ ((False → p3) ∧ ((False ∧ p2) → (p3 → p4)))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h13 : (True ∨ ((False → p3) ∧ ((False ∧ p2) → (p3 → p4)))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : (True ∨ ((False → p3) ∧ ((False ∧ p2) → (p3 → p4)))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756730858880307219107925389545 : (((p1 ∧ ((((False → p5) ∧ (False → True)) ∧ ((p2 → p4) → (p3 ∧ False))) ∨ (p1 ∧ (((p2 → p3) ∧ ((p5 → True) → p1)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738745665412809081954787063749 : ((((p2 ∧ p3) ∨ ((p4 ∨ (((p2 ∨ (p5 ∨ ((p2 ∧ (p5 ∧ p4)) → (p2 ∨ True)))) ∨ ((p2 → p2) → True)) → (p3 ∧ False))) → p4)) ∨ False) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 ∨ (p5 ∨ ((p2 ∧ (p5 ∧ p4)) → (p2 ∨ True)))) ∨ ((p2 → p2) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322299760233683713993325333674 : (p5 ∨ (((((p3 ∨ p1) ∧ p2) → ((True ∧ ((p5 ∧ (((False → True) ∨ p1) → (True ∧ (True → False)))) ∧ (p3 ∨ p3))) ∨ p2)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38283941804489660404175590442 : ((((((True ∨ p3) ∨ p3) ∧ (p4 ∧ (p3 → ((True ∧ (p5 → (p3 ∨ (p2 ∨ p5)))) → True)))) ∨ ((p1 ∨ p5) ∨ (p5 ∨ p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206403362940678507030429618850 : ((p3 ∨ ((True ∧ False) ∨ (p3 ∧ p1))) ∨ (p4 ∨ ((p4 ∧ p4) → (p1 ∨ (((p1 → p5) → (((p2 ∨ p1) → False) ∧ p1)) → (False → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263393078041727604615993001457 : (True ∧ ((((p3 ∨ p2) ∨ (((((False → p3) ∧ (True ∨ p3)) ∧ p1) → p2) ∧ (p5 ∧ False))) ∨ ((p1 ∨ False) → False)) ∨ ((False → False) ∨ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356305937154534078023916375092 : (p5 → ((p3 ∨ ((p1 ∧ p3) ∧ ((p1 ∧ ((p3 → p4) ∧ p2)) → ((p2 → p1) ∨ p1)))) → (((p2 ∨ (p1 ∨ (p1 ∧ p1))) ∨ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654221966432144266608520848283 : ((((((((p2 → (p3 ∧ p5)) → (((((True ∨ p1) → p5) → (p1 → True)) ∨ p3) ∧ p2)) → (False → p1)) → p3) ∨ True) ∨ (p3 ∧ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_171779067138196500279692702044 : (((((p5 → (p2 ∨ False)) → (p3 ∧ (False → (p4 ∧ p3)))) ∧ (p1 ∧ p1)) → p2) ∨ (((p2 ∨ p5) ∧ (False ∧ False)) → (True ∧ (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248275542876487277914305198789 : ((p2 ∨ p2) ∨ ((((p4 → p3) → (((p1 ∧ True) ∨ False) ∨ (p4 → p5))) ∧ (((p3 ∧ p2) → p4) → p5)) ∨ ((False ∧ False) ∨ (True → True)))) := by
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
theorem thm_5_vars_245479654291270858193928166981 : ((p2 ∧ p5) ∨ (((False ∨ (p2 ∨ (p3 ∨ (((p4 ∧ False) ∧ (True ∨ (p3 ∧ p4))) ∨ p3)))) → ((False ∨ p1) → p2)) ∨ ((p5 ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651026236976755868768064861161 : (((((p5 ∨ ((p5 ∧ (False → p5)) → p2)) → (p3 ∨ ((p5 ∧ (((p3 → p3) ∧ p1) → (p5 ∧ p3))) ∨ (p4 → p4)))) ∧ (True ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185774388811991433759851015233 : ((p4 → ((False ∨ p3) ∨ ((p2 ∧ p4) ∨ (p1 ∧ (True → False))))) ∨ (p5 → (((((p4 → True) ∨ p2) ∨ p1) → False) ∨ ((p5 → True) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_627485267481493795474363549055 : ((((((p5 → (p4 ∨ ((p2 ∧ p5) ∧ (True ∨ ((p4 ∧ p1) ∧ (((True ∨ (p1 ∨ True)) ∨ False) ∧ (p4 ∧ p5))))))) → p1) ∧ p3) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113182663190958963215596235491 : ((((((p4 ∧ (True ∧ ((p1 ∧ p5) → (((False → p1) ∧ p3) ∨ p5)))) ∧ (False ∨ p3)) ∨ (True ∨ p5)) ∧ p4) ∧ (p4 → p3)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209474451293732028582992679102 : ((p3 → ((True ∧ True) ∧ (False ∧ True))) → (p2 ∨ (((((True ∨ (((False ∧ True) ∧ p1) → (p3 → p5))) ∧ p5) ∧ False) ∨ (p3 → p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725674608905276670048612906752 : (((((True ∨ p1) ∧ p4) ∨ (((p4 ∧ p4) ∧ True) ∨ ((((((True ∨ p2) → p5) ∧ p4) → (p1 → (False ∧ p5))) → p3) ∨ (False ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217109384477071805123908227288 : ((((False ∨ False) ∨ True) ∨ p5) → (p3 ∨ (p3 → ((((((True → (p2 ∨ p4)) ∧ (False → p4)) ∧ p3) ∧ True) ∨ (p3 ∨ (p5 → p4))) ∧ p3)))) := by
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
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387396711194450785296779530339 : ((((((((p3 ∧ p3) ∨ ((p2 ∨ (p5 ∧ (False ∨ p2))) ∨ p4)) → ((p5 → p2) → False)) ∨ (p4 → True)) ∨ ((p4 ∨ p1) ∧ p4)) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185265155967341514498602548814 : ((p1 ∧ ((p3 ∧ True) → (p1 ∨ (False ∨ ((p2 ∨ p2) ∨ p3))))) ∨ (((((p1 ∧ p1) ∧ True) ∨ p2) → True) ∨ (p4 ∨ ((p3 ∨ p1) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174970494258921170999704689051 : ((True ∧ (p5 ∧ ((p4 ∧ (False ∧ (p4 ∨ (p4 ∨ (p3 ∨ True))))) → (p2 → p4)))) → ((p4 ∧ (((False → False) → p4) → False)) → (p1 ∧ p2))) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : ((False → False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h9
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h18 : ((False → False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h20 := h13 h18
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44154842524618956230340343726 : (((((False → ((p5 ∨ False) ∨ (((p4 ∨ (True → False)) ∧ p5) → ((p5 ∧ p5) → (p3 → p5))))) → p2) → ((p5 ∧ p4) ∧ p2)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732870989187468697306805457057 : ((((p2 ∧ p1) ∧ ((((p2 → ((False ∨ (((True → p3) ∨ p4) ∨ True)) ∨ ((p4 ∧ True) → p1))) ∨ (False → (p5 ∧ True))) → p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598627351138811479204600492395 : (((((p1 ∨ (p1 → p1)) → ((p2 → p1) ∧ (((((p5 ∧ p4) ∨ ((p5 ∧ p3) ∨ p1)) ∨ p2) → (p2 ∨ False)) ∨ (False ∨ p2)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680972741085236922012551093443 : (((((p1 ∨ p5) ∨ (p3 ∧ (p2 → (((True → (p3 ∨ p2)) ∧ (False → (p4 → (p5 ∨ p3)))) ∨ p2)))) → (False ∨ ((p1 ∨ p2) ∨ True))) ∨ p2) ∧ True) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66271031759046804649277574613 : ((p5 ∨ ((True ∧ (p2 ∧ p5)) ∨ (((((False ∨ (False ∨ p5)) ∧ p3) → p4) ∨ ((True ∧ (p2 → (p4 ∨ (p3 → p4)))) → p5)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112777953576304362060362665913 : ((((p5 ∨ (False ∨ ((p3 ∨ (p1 → p3)) ∨ p5))) ∧ ((((True ∧ (p3 ∧ (p4 → p5))) ∨ (p2 ∧ p4)) ∧ p3) ∧ p5)) → p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248768560325936418181803374301 : ((p3 ∨ p3) ∨ (((True ∧ False) ∧ ((p3 ∧ (p5 ∧ p1)) ∨ False)) ∨ (((p4 ∨ ((p5 ∨ p3) ∧ False)) ∨ (False → True)) → ((False ∧ p5) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_138145685931145406555094531464 : ((p1 → (((True → ((((p5 ∧ p4) ∨ (p5 ∨ p2)) → False) ∨ (p5 ∧ (p3 → ((False ∧ True) ∧ True))))) ∧ p2) ∨ p4)) ∨ ((p1 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801929256973806775780972234880 : (((p2 → ((p5 ∧ p1) ∨ ((((p4 ∧ p4) ∧ ((p2 ∧ p3) ∨ p4)) ∧ (((p2 ∧ ((True ∨ (True ∨ True)) ∨ p2)) ∧ False) → p3)) ∨ p2))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340880086759309338936260199291 : (p2 → ((((False ∨ ((p2 ∧ p4) → (((True ∨ (p1 → p4)) ∧ p5) → p2))) ∧ (p1 ∨ p2)) → (p5 ∧ (((p4 → p3) → p2) ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313281219498816084605450485565 : (p3 ∨ ((p3 ∧ ((p2 ∧ ((p3 ∨ ((p1 ∨ False) ∨ ((p3 ∨ (((((p3 → False) → p3) → p2) → p1) ∧ False)) ∨ p3))) ∨ p4)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



