variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197315423513979461608408381954 : ((((p5 ∧ p3) ∨ (p3 ∧ (p1 → p4))) → p4) ∨ (((p1 ∧ (p4 → (p4 → ((p1 ∧ p4) ∧ (p2 ∧ p5))))) ∧ (p2 ∨ False)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197328191036886389599927008509 : ((((True ∨ False) → ((p3 ∨ False) ∨ p4)) → p2) ∨ (((p5 → (((((True → True) ∨ p1) ∧ (p3 → (p2 ∨ p1))) → p1) → p3)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65384797741274018826014957460 : ((p3 ∨ (((p5 → ((p3 ∨ p2) ∧ (p5 → p2))) ∨ p2) → ((p4 ∧ (((False ∨ p2) → p4) ∧ (p5 ∧ p3))) ∨ (p1 ∧ (p1 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1798203041605721316001114369 : (((p1 → (p2 ∧ p5)) ∨ (((((p5 → p2) ∧ (True → (((True ∧ p3) ∧ p1) ∨ True))) ∧ p3) ∧ False) ∧ True)) ∨ (p4 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249293482305691427212807014750 : ((p4 ∨ p5) ∨ ((p5 ∨ (False ∨ (p1 → ((((p1 ∧ (p5 ∧ ((p1 ∨ p2) ∧ False))) ∨ (True → p2)) ∧ (p2 → (p3 → p1))) ∨ True)))) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62561209712625796728426401734 : ((p3 ∧ (p5 ∨ (((p3 ∨ (p1 ∧ (p2 → (False ∧ ((p3 → (p3 → p4)) → ((p2 → ((p3 → False) ∧ p5)) ∧ p3)))))) → p4) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737126726074962182462439484646 : ((((p3 → p4) ∧ ((((((False ∨ (p1 → False)) ∧ p2) ∧ p4) ∨ (p2 ∧ p4)) → (((p1 ∨ (True ∧ (p1 → p2))) ∨ p1) → p3)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233786070000802469684226423725 : ((p3 ∨ (p5 ∨ p3)) → (p3 → ((((p2 ∨ ((p3 ∨ (((p5 ∧ True) → (((p3 ∨ p2) ∧ p4) → p4)) → True)) ∧ False)) ∨ p3) → False) → False))) := by
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
    have h5 : ((p2 ∨ ((p3 ∨ (((p5 ∧ True) → (((p3 ∨ p2) ∧ p4) → p4)) → True)) ∧ False)) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : ((p2 ∨ ((p3 ∨ (((p5 ∧ True) → (((p3 ∨ p2) ∧ p4) → p4)) → True)) ∧ False)) ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : ((p2 ∨ ((p3 ∨ (((p5 ∧ True) → (((p3 ∨ p2) ∧ p4) → p4)) → True)) ∧ False)) ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118398810217781150459741262119 : ((p2 ∨ (((p2 ∨ p3) → True) → ((True ∧ p1) ∧ ((p2 → (((p4 ∨ (True ∨ ((p3 ∨ p2) → False))) → p3) → p4)) → p4)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158344998405394464050545499683 : (((p4 ∧ True) ∧ (p1 ∨ (True ∧ (p4 ∧ ((False → (p5 ∨ True)) ∨ ((p2 ∧ (p3 ∧ p5)) → True)))))) ∨ ((p5 ∨ False) ∨ (p3 → (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684145794690375039220415680988 : ((((((p3 ∧ ((((False ∧ (True ∧ p3)) ∨ True) ∧ (False ∧ p4)) ∧ False)) ∨ False) ∨ (p2 → True)) ∨ ((p3 ∧ (p1 ∨ (p4 ∧ False))) ∧ p4)) ∨ p1) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768330149857609241569045642480 : (((p5 ∧ ((((p1 → p1) ∨ (((p1 ∨ True) ∨ ((p1 ∧ p2) ∧ True)) ∧ (((p5 ∧ p3) ∧ p2) → p1))) ∨ p2) → (p4 → (p2 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196781828862452944372068483738 : ((((p2 ∨ False) ∧ (p5 ∨ (p1 → p3))) ∧ p4) ∨ ((((p3 ∧ (True → False)) → (p3 → (p1 ∧ (p4 ∧ (p3 → (True ∨ p4)))))) ∨ p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315162588402198945605194963790 : (p3 ∨ (((True → False) ∧ (True ∨ (p3 → p5))) → ((p4 → ((p2 → p1) → (((p3 ∧ p4) ∨ False) ∧ True))) ∧ ((p5 ∧ (p5 ∧ p3)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h19 := h12 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226254042525846497385461105313 : (((p3 ∨ p3) ∨ False) ∨ ((p3 ∨ (p3 ∨ p5)) → (p4 ∨ ((False → False) ∨ (p1 ∨ ((p4 → True) ∨ ((p3 ∧ ((p2 → False) → p2)) ∨ p4))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217968608682030940961714284941 : (((p2 ∧ p3) ∧ (p1 → True)) → (p3 → ((((False → ((True ∨ p2) → (p5 → True))) ∨ (p1 ∨ (True ∨ (p2 ∨ p5)))) ∧ p5) → (False ∨ p2)))) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h1.left
        let h20 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h19.left
        let h22 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h1.left
          let h26 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h25.left
          let h28 := h25.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h1.left
          let h31 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h32 := h30.left
          let h33 := h30.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113472647773285421685053156619 : (((((((p2 ∧ (p5 → (p5 → p5))) ∨ (p3 → (((True ∧ False) ∧ p4) ∨ True))) → False) ∧ False) ∧ (p3 → p2)) ∨ (False ∨ p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62779133196442717473108850475 : ((p4 ∧ ((p1 ∨ (p4 ∨ ((p2 ∧ False) ∧ (p2 ∧ (((False → (p2 ∧ (False ∨ False))) ∧ p5) → p2))))) ∧ (p4 → (p5 → (p4 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860111700975819144207183028613 : ((((((p5 ∧ ((p4 → p1) ∨ False)) ∨ ((((p1 → p4) → p5) ∨ p4) → (p3 ∨ (p4 ∧ (p4 → (False → p3)))))) ∨ (p4 → True)) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ ((p4 → p1) ∨ False)) ∨ ((((p1 → p4) → p5) ∨ p4) → (p3 ∨ (p4 ∧ (p4 → (False → p3)))))) ∨ (p4 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233854839805464866264076707645 : ((p4 ∨ (p3 ∧ p5)) → ((p2 ∨ ((p2 ∨ True) ∨ True)) ∧ ((p4 ∧ True) ∨ ((((p4 → (p3 ∨ p4)) → p1) → p2) → ((False ∨ p3) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52548995915633240526583780826 : (((((False ∧ ((p5 → (False ∧ p3)) ∨ (False → p5))) ∨ (p2 ∨ True)) → False) ∨ ((((p2 ∨ (p5 → True)) → (True → False)) ∨ True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57628403165668338846378992453 : ((((p2 ∧ p4) ∨ p3) → ((((False ∧ p4) → ((((False ∨ p1) → False) → p1) → False)) → ((p1 ∧ True) ∨ (p1 → (p2 ∨ False)))) ∨ p3)) ∨ p3) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797047396986001267247836770327 : (((p1 → ((((False ∧ (False ∨ (p3 ∨ (((False ∧ (p2 → p4)) ∧ (False ∨ p4)) → p2)))) ∨ p1) ∧ ((p4 ∧ p3) ∨ (p1 ∧ p5))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803285812443468806544200356157 : (((p3 → ((((((True → p3) ∨ p2) → (p4 ∨ (p2 ∨ (p2 ∧ (p5 ∧ False))))) ∨ p4) ∨ ((p3 ∨ p3) → (p1 → (p3 ∧ p5)))) ∨ p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614291766856098819998337630243 : ((((((False ∨ (p1 → (p3 ∨ (p3 ∧ p1)))) ∧ (p3 ∧ (False → (p3 ∨ (p4 ∨ (False ∨ (p4 → p2))))))) → ((p5 ∨ p1) → False)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_315846665564930644211251708830 : (p3 ∨ ((p1 → p1) → ((((p3 ∨ (p2 → (True → (True → p3)))) ∨ ((False ∧ True) ∧ (p3 ∧ (p4 ∧ p5)))) ∨ False) ∨ ((p4 ∧ p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114653431373948092032708224991 : ((((p1 ∧ ((p2 → (p3 ∨ p2)) ∨ (p2 ∧ p4))) ∨ (p1 → (p2 ∧ (False ∧ p5)))) ∨ (p3 → ((False ∨ (p3 ∨ p1)) ∧ True))) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8111146268081385695105866598 : (((((True ∨ (False → False)) → ((p3 ∧ (p2 → ((True ∨ (p1 → (p2 ∨ (True ∨ (p4 ∨ p1))))) ∨ True))) ∨ (p2 → p3))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_172111992760990901529065212589 : ((((((p2 ∧ ((False ∨ p2) → p1)) → False) ∨ p4) ∧ True) ∧ (p3 → (p2 ∨ p3))) ∨ ((p1 ∧ (p3 → p5)) ∨ (p1 ∨ ((p4 → True) → True)))) := by
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
theorem thm_5_vars_199762277134743431740821638904 : (((False → (p5 → (p2 ∧ (p4 → p2)))) → False) → ((((p4 → ((p3 → True) ∨ (p2 ∨ False))) ∨ p2) → p3) ∨ ((p3 ∨ (p3 ∨ True)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249864870065653525262470834447 : ((True → False) ∨ (((p3 → p2) ∨ (p4 ∨ p4)) ∨ ((((False ∨ False) ∧ p1) ∧ (((False ∨ False) ∧ (((p4 ∧ p3) ∧ p5) ∨ p5)) ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261135716359662720549583140036 : ((p4 → p4) → ((p5 ∨ (((p1 → ((((p2 → p3) ∨ ((p3 ∨ p2) ∨ p2)) ∧ (p3 → ((p5 → p3) ∧ p5))) ∨ p1)) ∨ False) ∨ p5)) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95746814215638411336889739069 : ((p5 ∧ (False ∨ ((((False ∧ p4) ∧ (((p2 ∨ p1) ∨ p4) ∨ p1)) ∨ p5) → (False ∧ (p3 → ((((p1 → True) ∨ p5) ∨ p3) ∧ True)))))) → p1) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((False ∧ p4) ∧ (((p2 ∨ p1) ∨ p4) ∨ p1)) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336410399035678851131069375526 : (p1 → ((p5 ∧ (False ∧ ((((p3 ∧ p3) ∧ (p3 → (p4 → ((p1 → p2) ∧ p2)))) ∨ (p5 ∨ (True ∧ (p1 → p1)))) ∧ (p1 → p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136003416424325093171900272234 : (((p3 ∨ (((p5 ∧ ((False → p2) ∧ p2)) ∨ p1) → p1)) ∨ ((p4 ∧ ((p2 → (p3 ∨ p3)) → (p5 ∧ p1))) → p4)) ∨ ((p4 ∨ p3) ∨ p4)) := by
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
theorem thm_5_vars_60587154767040315322705658673 : ((True ∧ ((True ∧ ((((False ∨ (p2 → True)) → (((p3 → (p4 ∨ ((p2 ∨ False) ∨ p2))) ∨ (True ∧ p4)) → p3)) ∧ p1) → p5)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695243858144162348699780808524 : (((((((((p1 → (p1 ∧ False)) → True) → False) ∨ (p5 ∧ True)) ∨ False) → False) → ((False ∧ ((p4 ∧ p5) ∧ ((True ∨ False) → p3))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704558251960757091941300634216 : (((((True ∨ p5) ∨ (p2 ∧ ((False ∨ (p3 → p3)) ∨ p2))) → ((p3 ∧ False) ∨ ((True ∨ ((False ∨ ((True ∨ False) ∨ True)) → p2)) ∨ True))) ∨ p2) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744838087891857685277509380640 : ((((p3 ∧ p4) → (((False → (p4 → (p2 ∨ ((p1 ∧ p1) ∧ p5)))) → (p2 ∨ (((((p5 ∨ p2) ∧ False) ∧ True) → p4) ∧ p2))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788515684628567580235545531173 : (((p5 ∨ ((p1 ∨ (((((p3 ∧ (((False ∧ (p1 ∨ p2)) ∨ p5) ∧ False)) → False) ∧ p2) ∧ ((p4 ∧ (p4 → p3)) → False)) ∨ True)) ∨ p2)) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113837683418635672961114034885 : (((p2 ∨ ((False → (False ∨ True)) → ((((p3 ∨ False) → (p2 ∧ (p1 → False))) ∧ p4) ∨ (p1 → (p1 → p1))))) → (p2 ∨ p4)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225066801336413862238428414885 : (((p1 ∧ p2) ∧ True) ∨ ((p1 → False) ∨ ((((p3 → (p2 ∧ ((p1 ∧ p1) → ((p5 ∧ (p5 ∧ (p4 ∨ p1))) ∧ p4)))) ∨ True) ∨ False) ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623743740121585844357720348351 : ((((p1 ∨ (((p4 ∧ ((True ∨ p1) ∨ (((p5 ∨ p4) ∧ p5) ∧ ((p2 → p1) → True)))) → (False ∨ p3)) ∨ (False ∨ (p3 ∨ False)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_55700096626180718377529514442 : ((((p3 ∧ (p2 ∧ p1)) ∨ True) ∧ ((True → p4) → (p4 → (((p1 ∧ (False ∨ p2)) → False) ∨ ((p4 → True) ∧ ((False → True) ∨ p1)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178088174035752798359825923573 : (((((False → (p5 → p1)) → ((p2 ∨ True) → (p2 → p5))) → False) → p4) ∨ ((True ∨ (p4 → p5)) ∨ (True ∧ (((False ∨ p1) → p4) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51440494743587527205352884243 : (((((p5 → ((p1 ∨ p4) ∨ p1)) ∧ ((p1 ∧ ((True → True) ∧ False)) → True)) → (p2 ∨ p5)) → (p1 ∨ (p3 ∧ (p5 ∧ (p4 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48677392303837613990657684911 : (((((p2 ∧ (p2 ∧ (((p4 ∨ p1) ∧ p2) → True))) → False) ∨ ((True → p2) → (True ∧ ((True → False) ∨ p5)))) ∧ (p3 → (p1 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265724855576639067604970689709 : (True ∧ (p3 ∨ (((p1 → p5) ∧ p1) ∨ ((p3 → (False ∨ ((True ∧ False) ∨ (p4 ∨ (p4 → ((p4 ∨ (False → p5)) ∧ p3)))))) ∨ (p1 ∨ False))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737863271227611064255876358461 : ((((True ∧ p1) ∨ (p1 ∨ (p3 ∨ (((p4 → (p5 ∧ True)) ∧ (p3 ∧ (p3 ∨ p1))) → (((p4 ∧ (p4 ∧ (p1 → p4))) ∨ p5) ∨ p3))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349115544797461462270095886887 : (p3 → (True → ((p5 ∧ (((p1 ∧ (p1 → (p1 → True))) → p3) → p5)) ∨ ((True ∨ p1) → (p4 ∨ ((True ∧ p3) ∨ (p2 ∨ (p2 → True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325829968097383819942386634619 : (p5 ∨ (p3 ∨ ((p1 ∨ False) → ((False ∨ (((((p5 ∨ (p4 → p2)) ∨ True) → False) → p1) → (p5 ∧ ((False ∧ p2) → True)))) ∨ (False ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618969338713380389755335011683 : ((((((p1 → p4) ∧ p2) ∨ (((True ∧ (p5 ∨ (False ∧ p4))) → (((p1 ∧ ((False ∨ p3) ∧ p3)) ∨ (p3 ∨ False)) ∨ p5)) ∨ p3)) ∨ p5) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192948922577252619656010895035 : ((((p4 ∨ p2) ∨ (p5 ∨ (p3 ∨ True))) ∨ (p2 ∧ True)) → (((True → p2) ∨ (((p2 → p2) ∧ (p5 ∧ p4)) ∨ p2)) → (p3 ∨ (p5 → True)))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h7
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
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
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h16
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h30
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h32
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h35
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h36 =>
            -- Disjunctions on the left can always be decomposed.
            cases h36
            case inl h37 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h37
            case inr h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h39
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h43
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h46 =>
          -- Disjunctions on the left can always be decomposed.
          cases h46
          case inl h47 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h48
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h49 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h50
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h51 =>
          -- Disjunctions on the left can always be decomposed.
          cases h51
          case inl h52 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h53
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h54 =>
            -- Disjunctions on the left can always be decomposed.
            cases h54
            case inl h55 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h55
            case inr h56 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h57
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h58 =>
        -- Conjunctions on the left can always be decomposed.
        let h59 := h58.left
        let h60 := h58.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h61
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245735631573597973131139640148 : ((p3 ∧ p2) ∨ (((p2 → (p2 → p5)) ∧ p2) → ((p2 → (((p4 ∨ ((True ∨ p5) ∨ (True ∧ p1))) ∧ (p5 ∧ p4)) → (p1 ∨ p5))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h7.left
        let h15 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h7.left
        let h18 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h7.left
      let h23 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348215177930124423853893069556 : (p3 → ((p2 → p3) → ((((p5 → (((p3 ∧ (p5 ∧ True)) ∧ (True → (p2 ∨ False))) ∧ p2)) ∨ p5) ∨ ((p3 → p1) ∨ False)) ∨ (p2 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245465696949707513576221880931 : ((p2 ∧ p5) ∨ (((p5 ∧ ((True → p2) ∨ True)) ∨ (((p1 ∨ (False → False)) ∨ ((p1 → p3) → (p5 ∨ True))) ∨ (p3 ∧ (p1 → p3)))) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793620527887782691357007826527 : (((True → (p4 ∨ (((p1 → (p3 ∧ (p4 ∨ p3))) ∨ ((p2 ∨ p4) ∨ (p1 ∨ (False → ((p3 ∧ p3) → p1))))) ∨ (False → (False ∨ p1))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355836857166678885229857710115 : (p5 → ((((((p2 ∨ p4) → (p1 → p5)) ∧ ((p4 ∧ (True ∧ p1)) ∧ (p1 → False))) ∧ ((p3 → p3) → p3)) ∨ False) ∨ (True ∨ (p2 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322439708458509572992796814016 : (p5 ∨ (((((p3 ∨ True) → p4) → False) ∧ ((((False ∨ (p1 → ((p3 ∧ False) ∨ p4))) → p1) ∨ (p4 ∨ (False → (p1 ∧ False)))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252754131908724726429335806291 : ((True ∧ True) → ((False ∧ ((p1 ∨ (((False ∨ p2) ∨ (False ∧ (p2 → (p3 ∨ p1)))) ∨ ((p5 → (p2 → (True ∧ p3))) ∨ p2))) → p1)) ∨ True)) := by
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
theorem thm_5_vars_658771319320351692406950298510 : ((((p5 ∨ (((p3 ∧ True) ∨ (True → ((p1 ∨ False) ∧ p5))) → (p2 → (p5 ∨ (p1 ∨ ((True → True) ∧ (True → p3))))))) ∨ (p5 → p5)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_31746441200131509649479309467 : ((False ∨ ((False ∧ ((p1 → ((p2 ∨ p5) → p5)) ∨ True)) ∨ (((False ∨ (((p4 → (p3 ∨ False)) → (p1 → p4)) → p1)) → p1) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118856055419471085588212680214 : ((True → ((((p3 ∧ (p1 → (True ∧ p3))) ∨ (p1 ∧ p1)) ∧ p1) → ((False ∧ p1) ∨ (((True ∧ True) ∧ (p3 ∨ False)) ∨ p2)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50266065491966489270888661179 : (((((p2 ∨ (p3 → (((p2 ∨ False) ∧ p5) ∨ (True ∨ False)))) → ((p5 → p2) → p5)) ∧ (False → False)) ∨ (p2 → (p5 ∧ (p3 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116353439627927918081348071974 : ((((p4 ∨ p5) ∨ p5) → ((((((True ∧ ((p4 → (p3 ∨ p1)) → p3)) → (p3 ∧ False)) ∨ p5) ∨ p1) ∨ p1) ∨ (p2 ∨ p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504252139178275177252254887097 : ((((p4 ∧ (p5 ∨ p5)) → ((p2 → ((p3 ∨ ((p1 ∨ (((p4 ∨ True) ∨ p2) → p4)) ∧ p2)) → ((False ∨ (True ∧ p4)) ∧ True))) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66767464896000085582242539214 : ((True → (p4 ∧ ((((p2 → (p1 ∨ False)) ∧ p1) → ((True ∨ p3) ∧ ((p5 ∧ True) ∨ (p4 ∨ ((p4 ∧ (True ∧ p2)) ∨ False))))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40220286313293960914310325412 : ((((True ∧ (((p2 → False) ∧ (((True → p3) ∧ (p1 ∧ ((True ∨ (p5 ∨ p1)) ∧ (p2 ∨ p1)))) ∧ (False ∨ p3))) ∧ p1)) ∧ p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65255980886732486059135635541 : ((p3 ∨ (((p3 → ((((p4 ∨ p1) ∨ p4) ∨ False) ∨ False)) → ((p2 ∧ (p5 → ((p3 → (p4 → (p1 ∨ p1))) → p5))) ∧ p4)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62664694728876746286951842266 : ((p4 ∧ (((True → ((p2 ∨ True) → (((p5 → p4) → p1) ∧ True))) ∨ ((p1 → (((p4 → (p3 ∧ True)) ∧ False) ∨ True)) → p4)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116170429664394469254021316899 : (((False → (p4 ∨ True)) ∧ (((p5 ∧ ((p3 ∧ ((p1 ∧ ((False ∧ (True ∨ p2)) ∨ (True ∨ p5))) ∨ p4)) ∧ p2)) ∨ p5) ∨ True)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52456713808592031379129565744 : (((p5 ∧ (p5 ∧ ((False ∨ (False ∨ (((p1 ∧ p5) ∨ p2) → True))) ∨ p4))) ∧ (((p2 ∨ p2) ∧ (p5 ∨ (p3 ∧ False))) ∧ (p1 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623386267257895639292466177415 : ((((False ∨ ((p4 ∨ ((False ∨ (p1 ∨ (p1 ∨ ((((((p5 ∧ (False → p4)) ∧ p1) → p2) ∧ True) ∧ p5) ∨ p5)))) → p5)) ∧ p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114481205825420421058320357798 : ((((False ∨ ((p2 ∨ p1) ∧ ((p5 ∧ ((p1 ∧ p2) → (p5 ∧ p2))) ∨ p4))) ∨ (True ∨ True)) → (False ∨ ((p2 → True) ∨ p4))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136427198764219755496454812542 : (((((p4 ∧ p1) → p5) → p2) → (((p1 ∨ (p2 ∧ (((False → ((p4 ∧ p3) ∧ p2)) → p1) → p4))) ∨ True) ∨ p4)) ∨ (False → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607619617279895870420429510033 : (((((p3 ∧ ((p3 → ((p1 ∧ ((p3 ∨ False) ∨ p4)) ∧ (p5 ∧ p1))) → (True → (((p3 → p3) → p5) ∧ (p1 → True))))) ∧ True) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177768093430753737447376280533 : (((True ∧ ((False ∧ p5) ∧ (p4 ∨ ((p4 ∨ (p1 → p5)) ∨ p3)))) ∧ p5) ∨ ((p3 ∨ (p3 ∧ False)) → (True ∨ (((p4 ∧ p3) → p3) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670303054456144694796694512771 : ((((((True ∧ p2) → False) ∧ (((p5 ∧ p2) ∧ (((True ∧ ((p1 ∧ p1) ∧ p3)) ∧ (p2 ∨ False)) ∨ p5)) ∧ p2)) ∨ (p2 ∨ (True ∨ p1))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_179612839951149433293510695346 : ((p3 → (p3 → ((p4 ∨ p4) → ((((p3 ∨ p1) ∨ p3) ∨ p4) ∧ p1)))) ∨ ((((p4 → p5) ∧ (p2 ∧ p1)) ∨ p2) ∨ ((False → False) ∨ p3))) := by
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
theorem thm_5_vars_696217612682749638531991386950 : ((((p4 ∨ ((((True ∨ p3) ∨ ((p5 ∧ True) ∧ False)) ∧ p3) ∨ (p3 ∨ p3))) → (((p2 ∨ p5) → True) → (True → (False ∧ (p4 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208836592526242670540259313448 : ((p3 ∧ (True ∨ (p2 ∨ (p1 ∧ p5)))) → (((False ∧ (p4 → ((p4 ∨ (((p3 → p4) ∧ p5) ∧ (p1 ∧ (True ∧ True)))) ∨ True))) ∨ p5) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86099506244299722456388710147 : (((p4 → (((((p3 ∧ p1) → False) → p2) ∨ p5) → p4)) ∧ ((True ∨ p1) → (p5 ∧ ((True ∧ False) ∧ ((p2 ∨ (p1 → True)) ∧ p1))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692706644855842657663769140771 : ((((((((p2 → p2) → True) → p1) → p2) → ((p2 ∧ (p2 ∨ p2)) ∨ p1)) ∧ ((False ∧ (p5 → p1)) → ((p1 ∨ (p3 ∧ p1)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66504996080683499602251564653 : ((True → ((p3 ∨ (((False ∧ (p3 ∧ (p1 → (((True ∨ p4) ∧ p2) ∧ p2)))) ∧ (((p2 ∨ (p5 → p5)) ∨ False) ∧ p2)) ∧ p5)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585639258277125680072898176556 : ((((((p3 → ((p1 ∨ p4) ∧ ((p2 → (p5 ∧ ((((p5 → p1) ∧ p1) ∨ ((True ∨ p3) ∨ p3)) ∧ p2))) ∨ p1))) ∨ p2) ∧ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47455486756029736841750927997 : (((p4 ∧ ((((p1 ∨ (p4 ∨ p2)) ∨ (p5 ∨ False)) ∧ (p1 ∨ p4)) → (p5 ∨ (((True ∧ (False ∨ p3)) ∨ p3) → p3)))) ∨ (p5 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118448890126855345978295937816 : ((p3 ∨ (((p3 ∨ (p4 ∨ p3)) ∧ ((((False → (p2 → ((False ∨ p5) ∧ p4))) → (True ∨ p2)) ∨ False) ∧ (p5 → p5))) ∧ p1)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707989688962206073840368724577 : ((((p1 ∨ (((p4 → p4) ∧ (p1 → p5)) ∧ p3)) ∨ ((((p2 ∧ ((False ∨ p2) ∨ p5)) ∨ (p4 → (p1 ∨ p3))) ∨ (p1 → p2)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_340805941638053130341824061889 : (p2 → (((p4 → ((p4 ∧ p4) → (((False ∨ (p1 ∧ ((p2 ∨ ((p3 → True) ∨ p5)) → (p5 ∧ (False ∨ p3))))) ∨ p3) ∨ p1))) → p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147698392025475307648509703049 : ((((p4 ∧ (((p4 ∨ p5) ∨ (False ∧ (p4 ∧ (True → p2)))) → p5)) ∨ (p1 ∧ ((p2 ∨ p4) → True))) → False) ∨ (((False ∨ True) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692937491449558634392652136668 : (((((p3 ∧ p3) ∨ (((p3 ∧ ((p2 → p2) ∨ p4)) ∧ True) ∧ (p1 → p5))) ∧ ((((p4 ∧ p3) ∧ False) ∧ ((p3 ∨ p4) ∧ p4)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265022876277718523355351622711 : (True ∧ (True ∧ ((((True ∨ True) ∧ p3) → ((((((p5 ∧ p2) → p5) ∧ ((p2 ∨ False) ∨ (p4 ∧ p3))) ∧ (False → p2)) → p2) ∨ True)) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41403184874612200603404804292 : (((((((p1 ∨ p1) ∨ p3) ∧ ((p5 ∧ False) ∧ (p5 → (True → p5)))) ∧ p1) ∨ (((True ∧ p3) → p2) ∨ (p1 → (p5 ∨ p1)))) ∨ p2) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681332119016561161886041287304 : ((((False ∨ (((p4 → p4) ∨ ((p4 ∧ (p1 ∨ (True ∨ p5))) ∧ False)) ∨ (((p4 ∨ p3) ∧ p2) ∧ True))) → (p3 → (False ∧ (p4 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651216962446040644039294848562 : (((((p1 → (False ∧ (p3 ∧ p4))) → (((p2 ∧ p2) ∨ ((p4 → True) → (p2 ∧ p2))) ∧ (False → ((p4 → p3) ∨ p1)))) ∧ (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_515039207155678778809895409926 : ((((p5 ∨ p4) ∨ (p4 → (p2 ∨ (((((False ∨ p3) ∨ (True ∧ (((p1 ∨ p3) → False) → ((p5 ∧ p1) ∨ p1)))) ∧ p3) ∨ p5) ∨ p4)))) ∧ True) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722283011949738562653831473 : ((((((False → p5) ∧ False) ∨ p5) → p3) ∨ (((p5 ∧ (p5 → p3)) ∨ (p3 ∨ True)) → (((True ∨ p2) → (p2 ∧ False)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810116146151204217206589978221 : (((p5 → ((p2 ∨ (((p5 → (False ∨ p1)) → (p1 ∧ (p2 → ((p3 → True) → (p3 ∨ True))))) ∨ p1)) → (p5 → ((True ∧ p4) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59014468390118427423000456713 : (((p3 ∧ p4) ∨ (((((p1 → (p2 → p1)) → ((p1 ∧ True) → ((p4 ∧ p1) → (p5 ∧ p5)))) ∨ False) ∨ p4) ∨ ((True → p1) → True))) ∨ p5) := by
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
theorem thm_5_vars_201252323053094526542952809356 : ((p3 → (((p5 → (p4 ∧ True)) ∨ False) → p2)) → ((p4 ∨ (p4 ∧ (p1 → False))) ∨ (((((p3 ∧ p2) ∧ False) ∧ p3) → p5) ∨ (p3 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



