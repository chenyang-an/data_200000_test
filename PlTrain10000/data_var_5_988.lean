variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140995365747369221310457482534 : (((True ∧ ((p1 → ((False ∨ (True → False)) ∨ p2)) → p1)) → ((p3 ∧ p3) ∧ (p1 → (p3 ∧ (p5 → (p5 ∧ p4)))))) → ((p1 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345618611707341324791543725810 : (p3 → ((True ∧ (((((False ∧ ((p5 ∨ p5) → p1)) ∨ ((p4 ∧ ((((p4 ∧ p4) → p1) ∨ p1) → p1)) ∧ p1)) ∧ p1) ∧ p2) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53045965036626031935817178456 : ((((False → False) ∧ (((p4 ∧ p2) → ((p5 → p5) ∨ False)) ∧ p4)) ∧ ((p4 → (p5 ∨ (p2 ∨ ((p2 ∨ p3) → (False ∨ p1))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113592366753338551628787639080 : (((p5 ∧ ((p2 ∨ (((p5 ∨ ((False → False) ∧ (p5 ∨ True))) → True) → (p1 ∧ (False → (p5 ∨ p5))))) ∨ True)) ∨ (True → False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180140520669719586992480429383 : ((((True ∨ ((p3 → ((p1 → (p4 → p5)) ∨ True)) ∨ p1)) → p5) → p4) → ((p5 ∧ (((p4 ∨ p5) ∨ (p3 → True)) ∧ (p3 → p5))) → p5)) := by
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
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738451071968047119124148540877 : ((((p1 ∧ p2) ∨ (p3 ∧ (p3 ∨ (((p4 ∧ (False ∨ ((((False → False) ∨ True) ∧ p1) → p4))) ∨ ((p5 → p4) ∨ (False ∧ p4))) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193001338298371721794580899015 : (((((p1 → (p2 ∨ p4)) ∨ False) → False) → (p3 ∨ True)) → ((p2 ∧ ((p1 ∨ (True → p5)) ∨ (False → ((True → True) ∧ True)))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177990439415190804287107215520 : (((p5 ∧ (((False ∨ p4) ∧ (p4 ∧ p1)) ∧ (p3 ∨ (p5 ∧ p5)))) ∨ p5) ∨ (((True ∧ ((p5 ∨ p2) ∨ True)) ∨ ((p1 ∨ p2) → p3)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_164842691131547544918277632154 : (((p3 ∧ ((p4 → (p1 ∧ p1)) ∧ (p4 → ((p2 ∨ (p5 ∨ p5)) ∧ (p4 ∧ p5))))) ∨ p4) ∨ (((p2 ∧ (p3 ∧ p5)) → (True → p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198667319658353839610611995397 : ((p4 ∨ ((p1 → ((True ∨ False) → True)) ∧ p3)) ∨ ((p4 ∨ ((p1 ∨ ((p1 ∨ p5) ∧ ((p4 ∨ p4) → True))) → (True ∧ (p3 ∨ True)))) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164316505922312925219905876233 : ((p2 → ((False ∨ (((((p2 ∧ (p4 → p3)) → (p5 ∨ p3)) ∧ p3) → p4) ∨ True)) ∨ p2)) ∧ (p2 ∨ (p3 → ((p5 → (True ∨ p1)) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172587889930528854085310399358 : ((((False → p1) ∨ p5) → (p5 ∨ (((p3 ∧ True) → (p2 ∧ (False ∧ True))) ∧ p3))) ∨ ((p5 ∧ (((p4 ∨ p2) ∨ (p5 ∨ False)) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55083060484371706773367062402 : (((False → ((p5 → False) → (p3 → p3))) ∧ ((((p1 ∨ p5) ∧ (True ∧ p4)) ∧ p3) ∨ (p3 ∨ (p2 ∧ (p5 ∧ ((True ∨ True) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659655110632632751558020580502 : (((((((p2 → (p1 ∨ True)) ∧ p1) ∨ (p5 → ((((p1 ∧ p3) → p2) ∧ p5) ∧ (p5 ∨ ((p5 → True) ∧ p1))))) ∧ p2) → (p3 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172592434268636356508247568668 : ((((p1 ∨ False) → p1) → ((p4 → (p1 ∨ (p2 → p3))) ∨ (True ∨ (p5 → p1)))) ∨ ((((p2 ∧ (p2 → p4)) ∧ (p4 ∨ p2)) → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679408961060094819121952473166 : ((((p5 → (((((p5 ∧ p1) ∨ (p2 → ((p5 ∧ (p2 → True)) ∨ (False ∧ p1)))) ∧ True) ∨ True) → p4)) ∨ ((p5 → (False ∧ False)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652685444246986443039432353465 : ((((p1 ∨ ((False ∧ p2) ∧ (((((p4 ∧ ((p5 ∧ p4) → p4)) ∨ False) ∧ p1) ∧ p4) → ((p3 ∨ p2) ∧ (True ∧ p4))))) ∧ (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710714000848789135041955160084 : ((((((p4 ∧ p2) ∧ True) → (p5 ∨ p5)) ∧ ((p5 ∧ (p1 ∨ (((p5 → (p2 ∨ (False ∧ p3))) ∨ p1) ∨ ((p2 ∨ p5) ∧ p3)))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37874975139862149993203240461 : ((((((p5 ∨ (((p3 → (False ∧ p2)) ∧ ((p4 ∧ (p3 → (p2 → p4))) ∨ True)) ∧ True)) ∨ (p4 ∧ True)) ∧ p4) ∧ (p1 → True)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671905873901393704917307720806 : (((((p2 → (((True → p3) → (p2 ∧ p4)) → (((True → (True → (False ∧ p3))) ∨ (p3 ∨ p2)) → p3))) ∧ p4) → ((p3 → p1) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62731883105478095179473671694 : ((p4 ∧ ((p1 ∧ (((p3 ∨ p5) ∨ ((((p3 ∨ p4) ∧ p3) ∨ p2) ∨ (False ∨ p3))) → ((p2 ∨ (p2 ∧ True)) → p5))) ∧ (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667060806490680522698019666921 : ((((((p1 → p2) ∨ p2) ∧ (True ∧ ((p4 → True) → ((p5 → ((p1 ∨ ((p5 → p3) ∧ False)) ∧ True)) ∨ p5)))) ∧ ((p5 ∨ p3) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187473481705103807035093298756 : ((False ∨ (((((p2 → p4) ∨ p5) ∨ (p1 → p1)) ∧ True) ∧ p5)) → (p4 ∨ ((p1 ∧ (False ∧ True)) ∨ (((p4 ∨ p3) ∧ (True → False)) → False)))) := by
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
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h12, we can now drive its conclusion.
          let h15 := h12 h14
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h12, we can now drive its conclusion.
          let h18 := h12 h17
          -- False on the left can always be used.
          apply False.elim h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h24 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h25 := h22 h24
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h28 := h22 h27
          -- False on the left can always be used.
          apply False.elim h28
    case inr h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h35 := h32 h34
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h38 := h32 h37
        -- False on the left can always be used.
        apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471421656377538172409617369030 : (((((False ∨ (((((p4 ∧ p5) ∧ p3) ∨ False) ∨ False) ∧ p2)) ∧ p2) ∨ ((True ∧ ((p5 ∨ ((p2 ∧ False) ∨ p1)) → (True ∨ p1))) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40138441850933890428303683684 : (((((p4 ∧ ((False ∧ ((p3 → True) → ((p4 ∨ p5) ∨ p2))) ∧ ((p1 ∨ p2) → p4))) ∨ ((p5 ∧ (True → p3)) ∧ p5)) ∧ p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205847793715330484626253229825 : (((p2 → p4) → (p1 ∨ (p5 → p1))) ∨ ((p5 → False) ∨ ((False ∧ (True ∧ (True ∧ (True ∧ ((p4 ∧ (p5 ∨ p1)) → p3))))) → (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_60313096948831130867638535493 : (((p1 → p4) → (((True ∧ (((p1 ∧ p3) ∨ p3) ∨ p4)) ∨ (((((True ∨ True) ∨ p1) → p4) ∨ True) ∧ (True → p3))) ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318855663744137139258450891927 : (p4 ∨ (((p4 ∨ (p2 ∧ (((p5 ∨ (p3 ∨ p5)) ∧ p5) ∧ ((((p5 → p5) ∧ p4) ∨ p3) ∨ (p3 ∨ p4))))) ∨ False) ∨ (True ∨ (p1 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110968511379590339870959835985 : ((((p4 ∨ (p2 → (((((p2 → True) ∧ True) → ((p3 ∨ (p1 → (p5 ∧ False))) ∨ p3)) → p4) ∨ p2))) ∨ (p3 ∧ p3)) ∧ True) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681259366290466960104674511890 : ((((p5 ∧ ((((p1 ∨ (p3 ∧ p3)) ∨ ((p2 → (p1 ∨ True)) ∧ ((p4 → p4) ∨ True))) ∨ True) ∨ p3)) → (((False ∨ p3) ∧ p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653649955267837669045094518181 : ((((((False ∧ ((((((((p1 → False) ∨ p4) → p2) → (p2 ∧ p2)) → (p5 ∧ p3)) ∨ p2) → p1) ∨ False)) ∨ False) ∧ p5) ∨ (p3 → p3)) ∨ p2) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355592728811404285568394744735 : (p5 → ((((p2 ∧ (True → p2)) ∨ p3) ∧ ((((p1 → p2) ∧ (True → (p1 ∧ False))) ∧ (p2 ∨ ((p5 ∧ p2) → False))) → p2)) ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148987854954977475485986238992 : (((p1 ∨ (p5 ∧ p1)) ∧ (p4 → (p2 ∨ ((((True → (False ∧ p4)) ∧ (True → p1)) ∨ p2) → (False → p5))))) ∨ (False ∨ (False → (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39166952178381173000672278517 : ((((p5 ∨ p1) → ((p3 → (((False ∨ ((True ∨ p4) ∨ (p1 → ((True ∧ p4) → False)))) → p1) ∧ p1)) → ((True ∨ p5) → p1))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777693774185105786990726081190 : (((p1 ∨ ((False ∧ ((p3 ∧ p1) → ((p3 → True) → p5))) ∨ (((p3 → ((((p1 ∧ (p5 ∨ False)) ∧ True) ∧ p4) → False)) → p4) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44892710335133988378451678306 : (((((p4 → False) → p1) → (((False ∧ (p1 ∧ (((True ∨ p3) ∧ (p5 → p1)) → p2))) ∨ (True ∨ p4)) ∧ ((p3 → p1) ∨ p5))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178166105229462231058192218996 : ((((p3 ∨ False) ∨ ((p4 → (p2 → (False ∨ p2))) ∧ (p2 ∧ True))) → False) ∨ (p3 ∨ (p4 ∨ (False → (p3 → (((p2 → p3) ∧ True) → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48575271225254532934957756310 : ((((p5 ∧ ((True ∧ p2) ∧ ((p5 ∨ (((p5 → p2) ∧ ((True ∧ True) → (p1 ∨ p3))) → p1)) ∨ p3))) → False) ∧ (True ∨ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42377134810055415323793244952 : (((p4 ∧ ((((True ∨ p5) ∨ (False ∧ False)) → ((((p4 ∨ ((True ∧ p4) → True)) → p4) ∧ p5) ∧ (p3 ∧ (p3 → p5)))) → p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262570047073047571289430871098 : (True ∧ (((((p3 ∧ (((p3 → p3) ∧ (True ∨ False)) ∧ ((True ∨ p5) ∧ (p4 ∧ (p3 ∨ p2))))) → (p1 ∨ (p3 → p3))) → False) ∨ False) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p3 ∧ (((p3 → p3) ∧ (True ∨ False)) ∧ ((True ∨ p5) ∧ (p4 ∧ (p3 ∨ p2))))) → (p1 ∨ (p3 → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h8.left
        let h13 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h13.left
          let h16 := h13.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- One of the premise coincides with the conclusion.
            exact h20
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h13.left
          let h23 := h13.right
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h25
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h27
            -- One of the premise coincides with the conclusion.
            exact h27
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h29 := h2 h3
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329560141368210795770783566392 : (True → ((p1 ∨ p3) ∨ ((p5 ∨ ((p4 ∨ p3) ∧ p2)) → ((p2 ∨ (((p2 → False) ∨ (p1 → ((True → p4) ∧ False))) ∨ p2)) → (False ∨ True))))) := by
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
    cases h2
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
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
      cases h2
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179200333952156688374030878689 : ((p3 ∧ (p3 ∨ (p5 ∧ ((p2 ∧ (((p5 ∧ p3) ∧ p2) → p2)) ∨ p3)))) ∨ (p3 → (p3 ∨ (p2 ∨ (((p4 ∧ p5) → p5) ∨ (p5 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153233493331915815645970000630 : ((True ∨ (False → (((False → p4) ∨ p2) → (((p1 ∨ ((((p1 ∧ False) ∧ p5) ∧ False) ∧ p4)) ∧ True) ∧ p5)))) → (p4 → ((True → False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177896844612841730400176639162 : ((((True ∧ (((p4 → (p5 ∨ p1)) → p5) ∨ p5)) ∧ (p5 ∨ False)) ∨ p4) ∨ ((p3 → (p5 ∨ (((p3 ∧ False) ∧ True) ∧ p1))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261046953011927556582805326335 : ((p4 → p2) → ((True → False) → ((p3 ∧ (((p2 → p4) ∨ p3) ∧ (p2 → (False ∨ (p2 → (p4 ∧ p5)))))) ∨ ((p2 ∨ p2) → (p1 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181255952375187325994116077282 : ((p4 ∧ (((p3 ∨ ((True → (False ∧ (p2 → True))) ∨ p3)) → False) ∨ p3)) → ((p2 → False) ∨ ((p5 ∨ ((p4 → True) ∧ (False ∧ p1))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153101936699106328153436191906 : ((p4 ∧ ((((p5 → p1) → ((p5 → p3) → ((p5 → True) → (((p1 ∨ p2) ∧ p1) ∧ False)))) ∨ p4) ∨ False)) → (((True → False) ∨ True) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190370812700765378794162438369 : ((((p2 ∨ p2) ∨ ((p5 ∧ p4) ∨ (p4 ∨ True))) ∨ p2) ∨ ((((p3 ∧ (p4 → p5)) → True) → p5) ∧ (((p3 ∧ (p4 → p3)) → p1) ∧ p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187312082240078465047025433562 : ((p1 ∧ ((False ∨ p3) ∨ (((True ∨ p5) ∨ True) ∨ (True ∧ True)))) → (((p4 ∧ (((p3 → p2) ∧ ((p2 ∨ True) ∨ p3)) ∨ p1)) ∨ p4) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h9
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52286564371399280192011643027 : (((p5 → ((((p5 ∨ p1) ∧ (p4 ∨ (p1 ∨ (p3 → (p5 → p4))))) → True) ∨ True)) → ((p3 → (p1 ∨ p5)) ∧ ((True ∧ p3) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210194057933705154212926588225 : ((((False → p4) ∨ p3) ∨ p4) ∧ ((p5 ∨ ((True ∨ False) ∧ (((p3 ∨ p3) → p5) → False))) ∨ (p1 → ((p1 ∧ ((p4 ∧ False) → p3)) ∧ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114375183184453515708155569413 : (((((((((p4 → p2) → (True ∨ p5)) ∨ p4) → p4) → (False ∧ (True → p2))) ∨ p1) → p4) ∨ ((True ∧ p1) → (True → p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49175196626885624497125029522 : (((((p1 ∧ p5) ∧ (False ∨ True)) ∧ (p1 ∨ (p1 → ((p1 → True) ∧ ((p4 ∧ True) ∨ ((p1 → p5) ∧ p4)))))) ∨ (p1 ∨ (False → p3))) ∨ p2) := by
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
theorem thm_5_vars_338235296615268600075098926524 : (p1 → (((p3 ∨ (p4 → p1)) ∧ (p5 ∨ False)) ∨ ((p5 ∨ p5) → (((p5 ∨ p4) ∧ p3) ∨ ((p1 ∨ p3) → (p4 → (p2 ∨ (p5 ∨ False)))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225510895435555980680856973633 : (((p5 ∨ p4) ∧ True) ∨ ((((False ∧ (p3 ∧ p2)) ∧ True) ∨ (p3 → p3)) ∨ ((p4 ∧ True) → (((p4 ∨ p5) → (p1 ∧ (p2 ∧ False))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55044098666422289636072641487 : (((p5 ∧ (p4 ∨ (True ∨ (True ∨ False)))) ∧ (p2 ∨ (p2 → (False ∨ (p3 → ((p5 ∧ p4) → (((p2 → False) ∨ (True ∨ p4)) ∧ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618571916412309210200326146859 : (((((False ∨ (p2 ∧ (p2 → p2))) → (False ∧ ((((p4 → (p1 ∨ (((p5 ∧ (False ∨ False)) ∧ p4) ∧ p5))) → p1) ∨ p2) ∧ p2))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_325612174826813944366305050076 : (p5 ∨ (False ∨ ((((p2 ∧ ((False → (((((p1 ∧ p2) → p5) ∧ True) → (p4 → (True ∧ p3))) → p2)) ∧ False)) ∨ False) ∨ (True ∨ p3)) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309313768132660910612853869766 : (p2 ∨ ((((False → p3) ∧ ((((p5 ∨ (((False ∨ (p3 ∧ False)) → (True ∨ True)) ∧ (p4 ∧ True))) ∧ p5) ∨ False) ∨ p1)) ∨ True) ∨ (p3 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115735367266719893600352809884 : (((((False ∧ p3) ∨ p4) → (p4 ∨ p2)) → (False ∧ (((p1 ∧ p2) ∧ p4) ∧ (p1 ∧ ((((p3 ∨ False) → True) ∧ p1) → False))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70475437962758718723350350397 : (((((((p3 → ((((p3 ∧ True) → p4) ∧ p3) ∨ p2)) ∨ False) ∨ (((p1 ∨ p1) ∨ True) ∨ p5)) → False) ∧ (p4 → (p3 ∧ p1))) ∧ True) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p3 → ((((p3 ∧ True) → p4) ∧ p3) ∨ p2)) ∨ False) ∨ (((p1 ∨ p1) ∨ True) ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355629331057597015614590164304 : (p5 → ((p3 ∨ ((p1 ∧ p4) ∧ ((p2 → (False → (p5 ∧ (True ∧ (False ∨ (p2 ∧ (((p3 → p5) → p2) ∧ p5))))))) → p3))) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135705833185537108842931404409 : ((((p1 → p5) ∧ (((p3 → (False ∨ p5)) → ((p2 ∧ False) ∨ p5)) ∨ p2)) ∧ (False ∨ (p2 ∧ ((p4 ∨ True) → True)))) ∨ ((p2 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311207120688895673629846512867 : (p2 ∨ ((p5 ∨ p1) → (False ∨ (p1 → (((p5 ∧ ((p4 → p4) → p5)) ∧ ((True ∨ p1) ∨ (((False ∨ p1) ∧ p4) ∧ (p3 ∧ p1)))) ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161091266985892507789401983201 : (((p3 ∧ p5) ∧ ((True ∧ (((True ∨ (p3 ∨ ((False ∧ p1) → False))) ∨ (p3 → False)) ∨ p5)) ∧ True)) → ((p3 → (p3 ∧ (False ∧ p4))) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300361671205432488772256714494 : (False ∨ ((((p3 → (p4 → p5)) ∧ ((((p5 → False) ∨ p2) ∧ ((p2 ∨ ((p2 ∧ p1) ∧ p1)) ∧ True)) ∨ True)) ∨ False) ∨ ((p4 → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338119328167525720842490451987 : (p1 → (((((True ∨ p3) ∨ (True ∨ True)) → p3) ∧ p4) ∨ (((((((True → (p3 ∧ False)) ∧ p5) ∨ (True ∧ p1)) → p4) → p4) ∨ p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((True → (p3 ∧ False)) ∧ p5) ∨ (True ∧ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41391315902819144306132180379 : ((((((p4 → (p4 → p3)) ∨ p2) ∨ (((p2 → p5) ∨ (True → True)) ∧ p1)) ∧ ((p1 → ((p2 ∧ p1) → p1)) → (p4 ∨ p1))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50096856007668558004281306886 : (((p3 ∧ (p2 ∨ (((p5 ∧ (((p1 ∧ ((p3 ∧ p1) ∨ True)) ∧ (p1 → p3)) → p1)) ∧ True) → p1))) ∧ (((True ∧ p5) ∧ p3) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175172951890034152798949884615 : ((True ∨ (((p5 → (False ∨ False)) → p4) → (True → (p5 ∨ ((p1 → p3) ∨ p2))))) → (((True → p5) ∧ ((p5 → p5) ∨ False)) → (p5 ∧ p5))) := by
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h18 := h13 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h21 := h13 h20
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58421181853181020139154090629 : (((p2 ∨ p3) ∧ (p3 ∨ ((((False ∨ p3) ∧ True) → (p5 ∨ (((p2 → True) → (((p3 ∧ (p3 ∨ p5)) ∨ False) ∧ p1)) → p5))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167900227443338832239052266818 : ((((p1 ∨ ((True → False) → True)) ∧ (p3 ∧ p1)) ∧ (((p3 ∨ (False ∧ p3)) → p2) → p3)) → ((False ∨ (p5 ∨ (p5 ∧ p4))) ∨ (p4 → p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h5.left
    let h12 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109566410347552223716992216911 : ((p3 ∨ ((p2 ∨ ((p2 → ((True ∧ ((p5 ∧ (p5 ∧ (True ∨ p5))) ∧ p4)) → p2)) → True)) → (((p5 ∨ p2) ∨ False) ∨ True))) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41531393156085134322774043027 : (((((((True ∧ (p1 ∨ p4)) ∧ p2) ∨ (p3 ∨ p3)) ∧ True) ∨ (((False ∨ ((p1 ∧ False) ∨ (p2 ∨ (p5 → p1)))) → p2) → True)) ∨ p4) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4099796315104446955274203435 : (p3 ∨ (((((((p2 ∨ True) → p2) → (((True → (p2 → p2)) → p3) ∧ True)) → (True ∨ p1)) → p5) ∧ p1) ∨ (False → (True → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340052110385533388499589235643 : (p1 → (p2 → ((p4 ∨ (True ∨ (((True ∨ False) → p1) ∧ (p5 → p1)))) → ((p1 → (((p3 ∨ ((False ∨ p4) → False)) ∧ True) ∨ p1)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216321843736037542951846001814 : ((p2 → (False ∨ (p2 → p5))) ∨ ((((False → False) ∨ p5) → ((p4 → True) ∧ (p3 → p2))) ∨ (p1 ∨ (True ∨ (((False ∧ p1) → p4) ∧ True))))) := by
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
theorem thm_5_vars_52671397696209427652011723738 : (((False ∨ ((p3 ∨ ((((True → p2) → p4) ∧ p2) → p3)) ∧ (True ∧ p5))) ∨ (False → (p2 → (p1 → (((False ∧ p4) ∧ p2) ∧ True))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313964960427665916862208002760 : (p3 ∨ (((((((p4 → p3) → p3) ∧ p1) ∨ (((True → ((False ∨ True) → p5)) → p4) → p3)) → p3) → ((p3 → True) ∧ p5)) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202684000703850426154269895005 : (((p5 ∧ (p3 → p2)) → (p4 → True)) ∧ ((p5 ∨ ((((((p4 ∨ p4) ∨ p4) ∧ (p2 ∨ (False ∧ True))) ∧ p5) → (p3 ∧ False)) ∨ True)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300785502181611394236232769924 : (False ∨ (((True ∨ (((p1 → p1) → p5) ∨ p4)) → (p3 ∧ (((False → True) ∧ True) → p3))) ∨ (True ∨ (False → (False ∨ (p4 → (False ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64784731501364173527216699956 : ((p2 ∨ ((((False → (((False → ((((True → (p4 → p1)) → p4) → p1) → p2)) ∧ p3) ∧ p5)) → p4) ∧ (p5 → (False ∨ p1))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140517351804870094884639983885 : (((p4 ∧ (((p1 ∧ p5) → p1) ∧ (((p2 → p2) → (p5 → p2)) ∧ (p4 → p5)))) ∧ ((p4 → (p3 ∨ p5)) → False)) → ((p5 ∨ False) ∧ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207220651710696266472894521259 : (((((p2 ∧ p3) ∧ p2) ∨ True) ∨ p4) → (p5 → (((p4 ∨ (p5 ∧ ((p2 → (p3 → p2)) → (p3 ∧ p1)))) ∨ p5) ∨ ((p5 ∧ p2) ∨ p4)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252991327527123500979810955981 : ((True ∧ p3) → (((p5 → p1) → ((((((p4 ∨ p2) → (p4 ∧ True)) ∧ p3) → (((True ∧ p1) ∨ p5) ∨ (False ∨ p2))) ∧ p2) ∨ True)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131879516539637791488394538809 : (((p2 ∧ False) ∨ (((p2 → p1) ∨ (p5 ∧ ((p3 ∨ ((p2 ∨ p3) ∨ ((p5 ∨ False) ∨ False))) ∧ True))) ∨ (False → p3))) ∧ (False ∨ (False → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114105311895625052350704910624 : (((p5 ∧ ((((p4 ∨ p1) ∨ ((True → (p3 ∨ (p3 ∨ (p5 → p2)))) ∧ (False ∨ True))) → p5) → p1)) ∨ ((p1 ∧ p3) ∨ p5)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308420405362808066848635524227 : (p2 ∨ ((((((True ∨ p5) ∨ (p5 → True)) → ((((True → True) ∧ (p5 ∨ True)) ∧ True) ∧ (True → True))) ∧ ((True ∨ p2) ∨ p2)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264431758459186743423909299965 : (True ∧ (((p1 → (True ∨ True)) ∨ True) → ((p2 → ((p2 → False) → (p1 ∧ False))) ∧ (True ∧ (p3 → ((((True ∨ p4) ∧ p3) ∨ True) ∨ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682181780392924278898259609193 : ((((((p3 ∨ (p5 ∨ p3)) ∨ ((p4 ∧ (((p1 ∧ False) ∨ (p1 ∨ p1)) ∧ p4)) ∨ p3)) → False) ∧ ((p4 ∧ p4) → (True ∨ (False → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311129283385662190350170765995 : (p2 ∨ ((p5 → p2) ∨ (p1 → ((p5 → False) ∨ ((((p2 → p2) → p5) → True) → (((p3 ∧ p3) ∨ ((p3 ∨ False) → p1)) ∨ (p5 ∨ p1))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260091395183988474100623287399 : ((p2 → False) → (p4 → (((p2 → ((((p1 ∧ True) ∧ (p5 ∧ (p3 → p5))) ∨ (True → p1)) → True)) → False) → ((p3 ∨ (p1 → p5)) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → ((((p1 ∧ True) ∧ (p5 ∧ (p3 → p5))) ∨ (True → p1)) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : (p2 → ((((p1 ∧ True) ∧ (p5 ∧ (p3 → p5))) ∨ (True → p1)) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h8
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601250597853864970866627766931 : ((((p2 ∧ (((p5 ∨ (p1 ∨ ((p4 ∧ (p4 ∨ ((p2 ∧ p2) ∧ p1))) ∨ p1))) → ((p1 ∧ p4) → (p1 → p4))) → (p4 ∨ p1))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135973843469724795908532220849 : ((((p3 ∨ (((True ∨ (p5 → p2)) → False) ∨ True)) ∧ p2) ∨ (p3 → ((p2 ∨ p5) ∨ ((p5 ∧ (p1 ∨ p1)) ∨ p3)))) ∨ (p3 ∧ (p5 → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_213379586347287252895588152999 : (((True ∨ (p5 ∧ p1)) ∧ p3) ∨ (p1 → ((((p5 → (False ∨ p2)) ∧ ((p4 ∨ (p3 → True)) → (p2 ∧ (p1 ∨ (p1 ∨ p3))))) ∨ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118606981801229461126392607680 : ((p4 ∨ ((((((p3 ∧ p4) ∨ ((p3 ∧ (p3 → False)) ∧ p3)) ∧ False) → p4) ∧ (p3 ∧ (p3 ∧ p3))) → (False ∧ (p2 → p5)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180227355961343603754399630720 : (((False ∧ ((((p5 ∧ (False → False)) → (p1 ∨ False)) ∨ p3) → True)) → p1) → (p3 → ((p1 ∧ ((p5 → (p5 → (False ∧ p4))) ∧ p3)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140710634265744635753505931261 : ((((p4 ∧ p5) ∨ (p2 ∨ ((p2 ∨ False) ∧ (p3 ∨ ((p3 → True) → p2))))) ∨ (((p5 → False) ∧ (p4 ∧ True)) ∨ p2)) → ((p3 ∧ p1) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
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
          -- False on the left can always be used.
          apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793631363338029811436772904211 : (((True → (p4 ∨ ((p5 ∨ p3) ∧ ((((p3 ∧ p4) → ((p1 → ((p4 → p4) → p5)) ∨ p3)) ∧ (p4 ∧ ((p3 ∧ p1) ∨ True))) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42594803934614329165791812067 : (((p2 ∨ (p2 ∧ (False ∨ (p1 ∧ ((((False ∨ ((p2 ∧ (p3 ∧ p4)) → (p5 ∨ ((p2 → p2) ∨ p4)))) → p4) → p1) → p2))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



