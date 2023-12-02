variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314108649456441234646848528482 : (p3 ∨ (((p3 → (False ∨ True)) ∧ ((((p2 → False) ∨ (p3 ∧ (False ∧ p4))) ∧ ((p1 → ((True ∨ p4) → True)) → p3)) ∧ p2)) → (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h24 := h22 h23
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662647935903089808053494143570 : (((((p2 ∧ (p1 → (p5 → p3))) ∧ ((p1 ∨ True) ∧ (p2 → (((((p2 ∧ p3) → p4) → (p2 ∧ p1)) ∧ p4) ∧ p3)))) → (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356977488325475457136426103430 : (p5 → ((p2 ∨ (p5 ∨ p3)) ∧ (((p1 ∨ p1) ∧ (((p4 → False) ∨ (p1 → (p2 ∧ p1))) → p2)) ∨ (p5 ∨ ((p4 ∧ (False ∨ p2)) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46664954989339213617283877348 : (((False ∨ (p2 ∧ ((False → False) ∧ ((p3 → p5) ∧ ((p1 ∨ False) ∧ ((False → (p5 ∧ (True ∧ p3))) ∨ (p3 ∧ p1))))))) ∧ (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51840072829990729376650246981 : ((((((((p4 ∨ (p3 → (p4 → p4))) ∨ p4) ∨ p1) ∧ (p3 → p2)) → p3) ∧ True) ∨ ((True ∧ p3) ∨ (True ∨ ((False ∧ True) → True)))) ∨ p4) := by
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
theorem thm_5_vars_219962000463624454632635540369 : ((p5 → ((p3 ∨ p2) ∨ p3)) → (((False ∨ (p4 ∨ ((p2 ∧ ((p4 ∧ (False ∨ (p4 → (p1 ∨ p5)))) ∨ (p4 → True))) ∧ p2))) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60250306968115212536285362303 : (((False → False) → (((p2 ∨ p3) ∧ (((((p3 ∨ ((p4 ∨ (p4 ∨ True)) ∧ (p2 ∨ (p5 ∨ False)))) ∨ p5) ∨ True) ∨ p3) ∧ False)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54643450884674550505807349808 : ((((p5 → (False → ((p4 → p4) ∨ True))) ∧ p1) → (True ∧ (p2 ∨ (False ∨ (((True → (p5 ∧ False)) → ((True → p4) ∨ p2)) ∨ p5))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318602341126804557857282301613 : (p4 ∨ ((((False → (p4 → ((False ∧ p1) ∨ p3))) → p1) ∧ (p1 → (p2 → (p3 ∨ (((p1 ∨ False) ∧ p1) ∧ (p2 ∧ False)))))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687020028110482086896927760443 : ((((p5 ∨ ((p1 ∨ (((False ∧ (p3 ∧ ((p3 ∧ (True → p4)) ∨ p5))) ∨ False) ∧ p1)) ∨ p4)) → (False ∨ ((p2 ∨ p5) ∧ (p3 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157362660315992180762683790029 : (((p2 → (((((p2 → ((False ∧ (p3 ∧ (p2 ∨ False))) → p3)) ∧ p4) ∧ True) ∧ p2) → p2)) → p3) ∨ ((p2 ∧ False) ∨ (True ∨ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66104831504387338977762343476 : ((p5 ∨ ((((p4 ∧ True) ∨ (p4 ∨ ((p1 ∨ False) ∨ (False ∧ p1)))) ∨ (True → ((p4 → (p1 ∨ (False → p2))) ∧ (p1 → p2)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792615660628863176920716712090 : (((True → (((p1 ∧ p4) ∨ ((p1 ∧ p3) ∧ p1)) ∧ (p2 ∧ ((p1 ∨ ((False ∨ False) ∨ p2)) ∨ (((p4 ∧ False) → p4) ∨ (p1 ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383154293739654218249939624286 : (((((p1 ∨ (p2 ∧ ((((p3 ∨ p3) ∨ (p4 → ((((p1 → p1) → p5) → (True ∨ p5)) → (p3 ∧ p4)))) → p4) ∨ p5))) ∨ p2) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_53852141366404142921383770803 : ((((p4 ∧ (p3 ∨ False)) ∧ ((p4 ∧ p5) ∧ (p5 ∨ False))) ∨ ((False ∧ (((p4 → p2) ∨ p1) ∨ True)) → (((p2 → True) ∧ p3) ∧ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111103127440737356839784692676 : (((((p1 ∨ (p3 ∧ p4)) → (p3 → (p5 ∨ (p2 → p4)))) ∧ ((((p5 ∧ ((True → p5) ∧ p1)) ∨ p5) ∨ p1) → p1)) ∧ p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744220457024867330960064983167 : ((((p1 ∧ p2) → ((p2 → (p4 ∧ (((True ∨ p3) ∨ False) ∨ ((p3 → ((True → (p5 → p4)) ∧ (p4 → False))) → p1)))) → (p3 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152263275814501575864095553584 : (((p5 ∨ (((p1 → p3) → p1) ∧ p1)) ∨ (((p3 ∨ False) ∨ (((p4 ∧ (p5 ∨ p5)) → p3) → p4)) ∨ p1)) → (p1 → ((False ∨ p1) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134126448958392273541934263298 : ((((False ∨ ((((p2 ∨ p5) → p4) ∧ (p1 ∧ p2)) ∨ ((p1 → ((p4 ∨ p3) ∨ p4)) → p3))) ∨ (p5 → p1)) ∨ False) ∨ ((False ∧ p2) → p5)) := by
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
theorem thm_5_vars_161108979689548798583546004215 : (((p1 ∨ p4) ∧ ((True ∨ ((p4 ∨ (False ∨ p5)) → (False → True))) ∧ ((p1 ∨ p1) ∨ (True ∧ p5)))) → ((p3 ∧ p4) ∨ (False → (True ∧ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- False on the left can always be used.
        apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h3.left
    let h29 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h35
      case inr h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h39
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- False on the left can always be used.
        apply False.elim h39
    case inr h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h43
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h43
        case inr h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h45
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h45
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h49
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- False on the left can always be used.
        apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138705596774847332852511566316 : (((((((p5 ∨ p1) ∧ (True → p1)) ∧ p1) ∨ p1) ∨ (p4 → (((p4 ∧ (True ∧ True)) → p4) → (p5 → p2)))) ∧ p2) → ((p5 ∨ False) ∨ p2)) := by
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
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620000738402840241608100697422 : (((((p2 → p5) ∧ ((True ∧ p1) ∧ (((((p1 ∨ p2) → ((True ∧ False) ∧ (p3 ∨ (p5 ∧ p1)))) ∧ p3) → p4) ∨ (p3 → p4)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_117504865066302789282428294772 : ((p2 ∧ (((p4 → p3) ∧ ((False ∨ ((p3 → (((True ∧ p3) ∧ p3) ∨ ((p2 → (p3 ∨ p3)) ∨ True))) → p1)) → p2)) ∧ p2)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168935218874484279984413576743 : ((True → (((((p5 ∨ (p4 ∨ (p3 ∨ True))) → p2) ∧ p5) ∧ p5) ∧ (p3 ∧ (False ∧ p3)))) → (p2 → (((True → p1) ∧ (p1 ∨ False)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200118451895003373610372184734 : (((p1 ∨ (p1 ∧ True)) ∧ ((p1 ∨ p1) ∨ p4)) → (((False ∨ ((True ∨ (p2 → (p4 → True))) → p4)) ∨ True) ∨ (True ∧ (p3 → (p5 → False))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_960304274639505589077016342225 : ((((p5 ∧ p2) ∧ (p5 → (((p3 ∨ ((p4 ∨ (p4 → (((p3 ∧ p1) → False) ∨ (p3 ∧ ((p4 → p4) ∧ p4))))) ∨ p1)) ∧ p3) ∧ p4))) → p4) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676075946328889427739352611859 : (((((p4 ∧ (p4 ∨ ((False → True) → p4))) ∨ ((p1 → ((p3 → p5) ∨ (p5 → (p5 ∨ p2)))) ∨ p1)) ∧ (p1 → (p2 → (True ∧ p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223359316640004553005040997967 : ((True ∨ (True ∨ p2)) ∧ ((((((False → p1) ∨ False) → (True ∨ True)) → (((p1 → p3) ∧ False) ∨ (((p3 ∨ p3) → p2) ∧ p4))) ∨ True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50923875681781359896761671129 : (((((p2 → p2) → (p4 → ((p5 → ((p2 → False) ∨ p1)) ∧ p5))) ∧ (True → (p1 → p5))) ∧ ((p3 → (p3 ∨ True)) ∨ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117709960806274035797160747217 : ((p3 ∧ (p4 ∧ (p5 ∨ ((((False → p3) → ((True ∨ p3) ∨ (p3 ∧ p4))) → (p5 ∨ (p2 → (p1 ∧ (True ∨ p1))))) → p3)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299975758652692610944934871284 : (False ∨ (((((((p5 → p4) ∨ ((p4 → (False ∧ p2)) ∨ p5)) ∧ p5) ∨ (p4 ∨ (p5 ∨ p3))) ∨ True) ∨ (p2 ∧ (p3 ∨ False))) ∧ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606433117232862105876603294122 : ((((((p2 ∧ ((p4 ∧ (p2 → p1)) ∨ ((p1 ∨ (((False ∧ True) → p2) → ((p5 → (p4 → p5)) ∨ p3))) ∧ p3))) ∨ p3) ∧ False) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116403343851794349916571064335 : (((p5 ∧ (True ∨ p1)) → (((p3 ∧ (p4 → p1)) ∧ p4) ∨ ((((p2 → (False ∧ p4)) ∨ (p1 ∧ p1)) ∧ p5) → (p2 → True)))) ∨ (p4 → p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159383500750760834853944264223 : ((((p4 ∧ (((p5 ∨ (p2 ∧ (p3 ∨ (False → p5)))) ∧ (p3 → (p5 ∨ p5))) ∧ p2)) ∨ p4) ∧ p2) → ((True ∨ p2) → ((p4 → False) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h36 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183913493217893618449788675717 : (((True ∧ (p5 ∧ ((p1 ∧ (p2 ∧ (p3 ∨ p4))) ∧ p1))) ∧ p1) ∨ (((((p2 ∨ p1) → (((p4 ∧ p3) ∧ p3) ∨ True)) ∨ p2) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804015840434638594534829885695 : (((p3 → (((True ∧ (p3 → p2)) → ((((p5 → (((p4 → p3) ∧ p3) ∧ False)) ∨ p2) → True) → (p4 → p1))) ∨ (p3 → (p5 ∨ p3)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168313108362082839779181483636 : (((True → False) ∧ (((p1 ∧ (((p4 ∨ True) → p1) → p2)) ∨ True) → ((p4 → p3) ∨ p2))) → ((True → (p5 ∧ p5)) → ((p2 ∧ False) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246182320762463619875014909311 : ((p4 ∧ p2) ∨ (p1 → (p3 → ((p1 ∨ p3) ∧ ((p5 ∨ True) → (p3 → (((p4 ∨ p2) ∧ (True → ((p1 → (False ∨ p5)) ∨ p5))) → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h15 := h13 h14
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h23 := h7 h22
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h25 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h26 := h24 h25
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33003737547850285862804038853 : ((p3 ∨ ((p4 ∧ (p5 → ((p5 ∧ ((p1 ∧ p4) ∨ p5)) → (p4 ∧ p3)))) ∨ ((True ∨ (p2 ∧ p2)) → ((p4 → (True ∨ p5)) → True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258521786792289751496022778098 : ((p5 ∨ p3) → (((((((p2 ∨ p5) ∧ p2) ∨ (False ∨ p5)) ∧ True) ∨ (p5 → (True → p5))) ∧ (False → (((p3 → True) → True) → p3))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205900009203252605482251130797 : ((True ∧ (p3 ∧ (p2 → (p5 ∧ False)))) ∨ (((((p4 ∨ ((((p1 → p3) → False) → p4) → p1)) ∧ (p5 ∨ p2)) → p2) → p3) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701134333257201597731161718149 : (((((True ∨ ((p3 → p1) ∨ ((p3 ∨ p1) ∧ p5))) → p4) ∧ (p3 → ((((False → p1) → p5) ∨ (p5 ∧ (False ∧ p3))) ∧ (p3 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159152661061499766214722131932 : ((p1 → (((((True ∧ True) ∨ (True ∨ p2)) ∨ (False → ((p1 ∧ p3) → (False → True)))) → False) ∧ p4)) ∨ ((p2 ∧ ((p4 ∨ p2) ∧ p2)) → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169556658021811784233618061169 : (((p1 → (((p4 ∧ p1) ∧ p3) ∧ ((p2 ∧ (True → True)) → (p1 → p5)))) ∨ True) ∧ (((p5 ∧ (((True ∨ True) ∧ p4) → p3)) ∧ p3) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679346516713179755129601190524 : ((((p3 → (((((p1 → False) ∨ p1) ∧ ((False ∨ (False → (p3 → p4))) ∧ (p5 → p1))) ∧ p4) → p5)) ∨ (p3 → (p3 ∧ (True → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717884425556609341333237427577 : (((((p1 ∨ (p1 ∧ p5)) ∧ True) ∨ ((False → p4) → ((p3 ∧ (((((p2 ∨ False) ∨ p4) → ((False ∨ p2) ∧ p3)) → True) ∨ p5)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227962266005451423922031776493 : ((p3 ∧ (True ∨ True)) ∨ ((((False ∨ ((p1 → (p4 → False)) ∧ False)) ∨ (p5 ∨ p5)) ∧ (((False ∧ p1) ∨ p5) → ((False → True) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165567218246856763483542068563 : (((((p1 ∨ (True → p3)) ∧ (p2 → p1)) ∨ p5) ∨ (((p3 ∧ p3) ∨ p4) ∧ (p4 ∨ p1))) ∨ ((True ∨ False) ∧ ((True ∨ (p4 ∧ p4)) ∨ p1))) := by
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
theorem thm_5_vars_118171508453795560576448699616 : ((False ∨ ((p2 ∨ p4) → ((True ∨ p5) ∧ ((p4 ∨ (True → (((p1 → (p5 → False)) ∨ ((p5 → p4) ∧ True)) ∧ p3))) ∧ False)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667961784095689703285849899464 : ((((p3 ∨ ((p1 ∧ (p2 ∨ (True ∧ (p1 ∨ p3)))) ∨ (False → ((((p4 → (True ∧ p2)) → p4) → True) → p4)))) ∧ (p5 → (True ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173390789634301979553306316777 : ((p4 → (((p3 → p5) ∨ (p5 → p4)) → ((p3 ∧ ((p2 ∨ p2) ∨ p4)) ∧ p2))) ∨ (((True ∧ p4) ∧ (p4 ∨ True)) ∨ (False → (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157839296374451601640767632962 : (((((p2 ∧ p3) ∨ (((p2 ∨ True) ∨ p2) ∧ p4)) ∧ p1) ∧ ((p4 ∨ ((p3 ∨ p3) → p2)) ∨ p4)) ∨ (True ∧ (p2 → ((p2 ∨ p2) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690750281431783846177773658538 : (((((((True ∨ (p4 → p4)) ∨ (p4 ∧ ((p5 ∧ p3) ∨ (p4 ∨ p2)))) → p3) → p1) → (((p1 → False) ∨ (False → (p3 ∧ p4))) ∨ False)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3294742948024706459632289641 : ((True ∧ p3) → (((p3 ∧ (p1 ∨ p1)) ∨ (p3 → ((p2 → ((False → (True ∧ p2)) ∨ False)) ∧ False))) → (p1 ∨ ((p1 ∨ p5) ∨ p2)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49131441538547622270029820829 : (((((p5 → (((False ∨ p4) ∧ p1) ∨ (p5 ∧ (False ∧ p1)))) ∨ p5) → ((p3 ∧ True) ∧ ((p2 → p1) ∨ p1))) ∨ (False ∨ (False → p1))) ∨ False) := by
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
theorem thm_5_vars_135198936793868210345091631941 : ((((((((p1 → (p3 ∧ p4)) ∧ (True ∨ (p5 ∨ p2))) ∧ True) ∧ p2) → (p4 ∧ p1)) ∧ (True ∧ p5)) → (True → p2)) ∨ ((p3 → p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65521742454307506229393656279 : ((p3 ∨ (p2 ∨ (((p4 ∨ p4) ∨ (((False → p2) ∨ (((p2 → p3) ∧ (p2 ∧ p3)) ∨ p4)) ∨ p4)) ∧ (p3 ∨ ((p3 ∨ p4) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431259562401212374325150657212 : ((((True ∧ (p4 ∧ (((p2 ∨ (p1 ∨ p4)) ∧ ((False → ((p3 ∨ (p1 ∧ False)) → True)) → (True ∧ p5))) ∧ (p1 → p5)))) ∨ (False → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_761517400197794228207169412952 : (((p3 ∧ ((((True ∨ (p1 → False)) ∧ ((p2 ∨ (((p4 ∨ p4) ∧ p3) ∧ p2)) → (((p5 ∨ p4) ∨ p2) → (p4 ∧ p3)))) ∧ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228538667560951547596226102477 : ((p1 ∨ (p3 ∧ p2)) ∨ ((False ∨ False) ∨ (((((((True ∧ ((p4 ∨ False) ∨ (p3 ∨ (p3 ∧ True)))) → False) ∨ p2) → p5) ∨ False) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113428904867135091899726268394 : ((((((((p4 ∧ p2) ∧ (((p2 ∧ True) ∧ p1) → (((False ∨ False) → p2) ∧ p5))) ∧ p4) ∧ p5) ∧ p2) ∨ False) ∨ (True ∧ True)) ∨ (p1 → p4)) := by
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
theorem thm_5_vars_62541577592225439004992707971 : ((p3 ∧ (p1 ∨ (((p4 ∨ p1) ∧ p5) → ((((p1 → True) → ((p1 → (p5 ∨ p4)) ∨ p1)) → (((False ∧ p3) ∧ False) ∨ False)) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208815297053556342177243944479 : ((p3 ∧ (((p1 ∧ p3) ∨ False) → p5)) → (((p4 → False) ∧ (((p3 ∨ p5) → p4) ∨ (p4 ∧ (False ∧ (p4 ∧ p4))))) → ((p3 ∧ p2) → p1))) := by
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
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : (p3 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301530334644665492175925325577 : (False ∨ (((p2 ∧ p5) ∨ p5) ∨ (((p4 → p2) ∧ p1) ∨ (((p4 → True) ∧ ((False ∨ p5) ∨ p5)) → ((p3 ∧ p2) → (False → (p3 ∨ p2))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328680410610288636962079542609 : (True → (((p1 ∧ p5) ∨ (True ∧ ((p2 ∨ (p3 ∧ p4)) ∨ (p3 ∨ True)))) ∧ (((p5 ∨ p5) → (((p5 ∧ p1) → (True ∧ p3)) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248586936689871740329551639519 : ((p3 ∨ False) ∨ ((True ∨ (p5 ∨ (p2 ∨ (False ∨ (p2 ∨ p2))))) → (p5 ∨ (True ∧ ((((p1 → p2) ∨ (p4 ∧ (p5 ∧ p3))) ∧ False) → p5))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h5
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- False on the left can always be used.
          apply False.elim h18
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h29
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- Disjunctions on the left can always be decomposed.
            cases h30
            case inl h32 =>
              -- False on the left can always be used.
              apply False.elim h31
            case inr h33 =>
              -- Conjunctions on the left can always be decomposed.
              let h34 := h33.left
              let h35 := h33.right
              -- Conjunctions on the left can always be decomposed.
              let h36 := h35.left
              let h37 := h35.right
              -- False on the left can always be used.
              apply False.elim h31
          case inr h38 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h39
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- Disjunctions on the left can always be decomposed.
            cases h40
            case inl h42 =>
              -- False on the left can always be used.
              apply False.elim h41
            case inr h43 =>
              -- Conjunctions on the left can always be decomposed.
              let h44 := h43.left
              let h45 := h43.right
              -- Conjunctions on the left can always be decomposed.
              let h46 := h45.left
              let h47 := h45.right
              -- False on the left can always be used.
              apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40558892079626989506767934298 : ((((p2 → ((((True ∧ (((p3 ∧ False) ∧ p5) ∨ (p4 → (p4 → p2)))) ∧ True) → (((p2 ∧ p3) ∨ p1) ∧ p5)) → p3)) ∨ p3) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61826374226452287180048461617 : ((p2 ∧ ((p5 ∧ (((((p1 ∨ ((p4 ∨ True) → p4)) ∨ p3) → p3) ∨ (p3 ∨ (p4 ∧ (p4 → p5)))) → (p3 ∧ (p5 → True)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327079490963489848938875751608 : (True → (((p3 ∨ (p2 ∨ p5)) ∧ (((p3 ∧ False) ∨ (((p2 → False) ∨ p4) ∧ (p1 ∨ (p3 → (False ∨ (False → (True → True))))))) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113222982705844400674416506286 : (((((p5 ∧ ((True → ((p1 → p5) → ((False ∨ (p5 → p1)) ∨ (True → False)))) → (p5 ∨ p1))) ∨ p1) → p4) ∧ (True → False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696513775469313286741650540314 : (((((p5 ∧ ((p1 → (p3 ∧ (p3 ∨ (False ∨ p1)))) → False)) ∧ False) ∧ ((p4 ∧ True) ∨ ((p5 ∨ (False → (p3 → True))) ∨ (False → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112278775075762931705478804392 : (((True → (((p4 ∧ False) ∨ True) → (False ∧ ((p2 ∧ (p3 ∨ (((p4 ∧ True) → False) → (p3 ∨ p5)))) ∨ (p1 ∧ p1))))) ∨ True) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160022160791836345633502607930 : (((((p1 ∨ False) ∨ p1) → (((((False → False) → p5) → p1) ∧ ((p5 → False) → p4)) ∨ p4)) → p2) → (p5 ∨ (p3 ∨ (False ∨ (False → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342195400049515962852527692471 : (p2 → ((((p4 → ((((p5 → p4) ∧ p1) ∧ (p1 ∧ p3)) ∧ (p3 → (p2 ∧ p2)))) → (True ∨ False)) → p3) → ((True → p4) → (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313226732286883943834445441736 : (p3 ∨ (((p3 ∧ p4) ∧ ((((p1 → False) ∨ p3) → p5) → ((False ∨ p5) → ((p1 ∨ (p5 ∨ p3)) → (p3 ∧ (p3 ∧ (p2 ∨ p4))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305492419748638824664422534625 : (p1 ∨ (((True → (p3 ∨ ((((p4 ∧ True) ∧ (p1 ∨ p3)) ∧ p3) ∨ True))) ∨ p4) ∨ ((((p1 ∨ p1) ∨ ((True ∨ p2) → p1)) → p3) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104569414000106882729086728551 : (((((((p4 → p4) ∧ p4) ∨ p3) ∧ ((True ∨ False) → ((p1 ∨ (True ∧ p3)) ∧ p3))) ∨ (p2 ∨ (False → p5))) ∨ (p1 ∧ True)) ∧ (True ∨ True)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114515258880057329967682200780 : ((((p2 → p1) → ((p5 → p1) → ((p1 ∨ p4) ∧ ((((True ∧ p2) ∧ True) → True) → True)))) → ((p3 ∨ False) ∧ (p1 ∧ p5))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165556595135845903647544928728 : (((p5 ∧ ((p5 ∧ (p1 ∧ p4)) ∧ (p1 ∧ p4))) ∧ (((p1 ∨ False) ∧ (False → p1)) ∧ p2)) ∨ ((False ∧ p4) → (p2 ∧ ((False ∨ p2) → False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124509139020671547899554345300 : ((((p4 ∧ (False ∧ False)) ∨ (True → False)) ∧ ((p1 ∨ (p1 → ((True ∨ (((p1 → p5) → False) → False)) ∨ (True ∨ False)))) ∨ p5)) → (p2 → p3)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h14 := h10 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h17 := h10 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h20 := h10 h19
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40233865154314260716192771214 : ((((p2 ∧ (p2 ∧ ((((((p1 ∨ (p2 ∨ ((p5 ∧ p2) → p4))) ∨ p2) ∧ ((p3 ∨ p3) ∧ True)) ∨ p4) ∧ True) ∧ p3))) ∧ p4) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111196557045308179111240792177 : ((((True ∨ (p1 ∧ p4)) ∧ ((((True ∨ True) ∧ ((p4 → (p2 ∧ p1)) → p4)) → p1) ∨ ((p2 ∧ p4) → (True ∨ p1)))) ∧ True) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650873583554844988959035292619 : (((((p1 → ((True ∧ ((p4 ∨ p1) ∧ p3)) → False)) → ((p1 ∨ p5) → (p4 ∨ ((p5 ∧ ((p3 ∨ True) → p5)) ∨ p2)))) ∧ (p5 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345861427030404954473030360979 : (p3 → ((((True → (p4 ∨ False)) ∧ (((((p5 ∧ (p5 ∨ p1)) → (False → p5)) ∨ (p4 → p2)) ∧ p1) ∨ (p5 → p4))) ∧ (True → p3)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h22 := h5 h21
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251115074375972924113980810301 : ((p2 → False) ∨ ((p1 ∨ (p2 ∨ (((((p5 ∧ p4) → p3) → (True ∨ (p5 ∧ p1))) → (p3 ∧ ((p5 ∧ p4) ∧ False))) → (p3 ∧ p1)))) ∨ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ p4) → p3) → (True ∨ (p5 ∧ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((p5 ∧ p4) → p3) → (True ∨ (p5 ∧ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683956835338683532320267723591 : ((((((False ∨ (((True ∧ p2) ∨ ((p3 → p2) → (p5 ∧ True))) ∧ (p3 ∨ p4))) → p2) → p3) ∨ (p4 → ((False → p2) ∨ (True → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157654380492953612736613311037 : (((((p3 ∨ ((p2 ∧ (True ∧ p1)) ∨ (p4 ∨ False))) → (p2 ∨ False)) ∨ p4) ∨ ((p2 ∧ p1) → p2)) ∨ ((p3 ∧ (p5 → (p1 ∧ p2))) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_351536665089519844943247608922 : (p4 → ((((p4 ∨ p4) ∨ p4) ∧ ((p3 ∨ ((False ∧ (False ∨ p2)) → ((False ∨ p3) ∧ p2))) → p3)) ∨ ((p3 ∨ (p2 ∧ p3)) → (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49333177112679704824009816715 : (((p5 ∨ ((p1 → p2) ∨ (p3 ∨ ((True → (((p3 ∧ (p3 ∨ p3)) → (p1 → (True ∧ p2))) → p4)) ∧ False)))) ∨ ((False ∨ p4) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198233264932619031230420048406 : ((True ∧ ((p2 → (p1 ∧ p1)) → (p4 → p5))) ∨ (((p2 ∧ (p1 ∨ p4)) ∨ p4) ∨ (((p5 ∧ False) ∨ (True ∨ (p3 → False))) ∨ (False → p4)))) := by
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
theorem thm_5_vars_262291730881109487873959132076 : (True ∧ (((((p2 ∧ (True → ((p3 → p1) ∧ p4))) ∧ (False ∨ p5)) ∧ (p2 ∧ p1)) ∧ ((True ∧ p1) → ((p5 ∧ p2) ∨ (p4 ∧ True)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49096918765375347275084392387 : ((((p4 ∧ ((((p2 → p3) ∨ True) → ((p5 → p5) ∨ (p3 ∨ False))) → (False ∨ p2))) ∨ (p4 ∧ (False → p3))) ∨ ((p5 ∨ p1) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308538064299917756830939310973 : (p2 ∨ ((((((p5 → p4) ∨ (True ∧ p5)) → False) ∨ ((False ∨ p3) ∧ p3)) → (True → (((p2 ∧ (p4 → p1)) ∨ p1) ∨ (False → p2)))) ∨ p4)) := by
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
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41786796460164520781067009189 : ((((((p3 ∨ p2) ∨ p2) → p2) → ((((((p5 → (p5 ∧ (False ∨ p3))) ∧ True) ∨ p3) ∨ (True ∨ (p3 → p2))) ∧ False) ∧ p5)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150090879670347352481987751695 : ((True → (p3 → (p1 ∨ (p4 ∧ (((False → p4) ∧ p4) → ((p1 → (p2 → ((p2 ∧ p5) ∧ True))) ∧ p2)))))) ∨ (True → (p1 ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_441952516268543606579608461974 : (((((((False ∨ (False ∨ ((p4 ∧ (((False ∨ p4) → p5) → p5)) ∨ True))) → (p2 ∧ p3)) → (p1 → False)) ∧ p1) ∨ (p4 → (p5 → p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53844499888491081454460865670 : ((((((p4 ∨ p2) → False) ∨ p4) → ((p5 ∧ p4) ∧ p4)) ∨ ((((False ∨ (p5 ∧ p3)) ∨ (p3 ∨ p2)) ∨ p5) → ((True ∧ p2) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725487709112818108751227264646 : (((((True ∧ True) ∧ p5) ∨ (((p1 ∨ p4) ∧ (p1 → ((p3 ∨ p2) → (p3 → p5)))) ∨ ((((False ∨ p1) ∨ (p1 → p2)) → p3) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114414982601165952997546932114 : ((((p4 ∧ False) ∧ (p1 ∨ (((((p1 ∧ p1) ∧ (p1 → p4)) ∧ p1) → (p5 → p2)) ∨ p1))) ∨ (p1 ∧ ((False → p1) ∧ p4))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133850082751819636211420726082 : (((False ∧ (((p4 ∨ (((p3 ∧ p5) ∨ p2) ∧ ((p4 → ((p1 ∧ p3) ∧ p2)) ∧ p1))) ∨ p4) ∧ (p4 ∨ p1))) ∧ p4) ∨ (p1 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



