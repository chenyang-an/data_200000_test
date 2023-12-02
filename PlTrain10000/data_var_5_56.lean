variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258853513820596996692946671416 : ((True → p1) → (((p3 ∧ p4) → (p3 → p2)) → (((p4 ∧ True) ∧ p5) → (p2 → (p5 ∧ ((p1 ∧ (p5 ∨ p4)) → (p5 → (p2 ∨ p5)))))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h3.left
    let h20 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62425312899680504030204273438 : ((p3 ∧ ((p2 ∧ (p1 ∧ (p5 ∨ False))) ∧ ((p5 ∧ ((True → p1) ∧ (p4 ∨ p4))) ∧ (p3 → (((p5 ∧ p5) → (p4 ∨ p1)) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802146811407799736773894856976 : (((p2 → (p1 ∧ (((((p2 → ((((p3 → True) ∧ p2) → p4) ∨ (((p1 → (p1 ∨ p1)) ∨ p3) ∧ p1))) ∨ p5) ∧ p4) ∨ False) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731673007965849937171565405164 : ((((p2 → (p3 ∧ p2)) → (p2 → ((p3 ∧ ((p5 → ((p2 ∧ (False ∨ p5)) → p1)) ∧ (True ∧ (p1 → (p1 ∨ p1))))) ∧ (p5 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165512220325811800191317849368 : (((((p3 ∨ ((p2 ∨ (p1 → p2)) → p4)) → p4) → p3) → ((p3 ∧ (True ∨ p4)) ∧ p3)) ∨ (True ∧ (True ∨ (((False → False) ∧ True) ∧ p1)))) := by
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
theorem thm_5_vars_149125115113481033184488782119 : (((p2 ∧ False) ∧ (((p3 → (p2 → ((False → p3) → (p5 ∧ ((True → True) ∨ (p1 ∧ False)))))) → p1) ∧ p5)) ∨ (p1 → (p5 → (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67853793104534140778915919869 : ((p2 → (((p5 → (True → p4)) ∨ (p3 ∨ ((((p4 ∧ p2) ∧ ((((True ∨ p5) → p5) → p4) → p3)) → p2) ∧ p3))) → (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692351486927712843639351829424 : ((((((False ∨ (p2 ∨ ((p4 ∨ False) ∨ p1))) → ((p4 → False) ∨ p3)) → p3) ∧ ((p4 → ((p2 ∨ ((p4 → p5) ∧ p2)) → p3)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328123571117808373382417518002 : (True → (((p4 ∨ ((p4 ∨ p4) → ((p5 ∧ p5) ∨ True))) ∧ (p1 → (False ∧ ((((p2 → p5) → p1) → p1) ∨ False)))) ∨ (p5 ∨ (True → True)))) := by
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
theorem thm_5_vars_942849070548275143850509233825 : (((((p2 ∧ p4) ∧ (p4 → False)) ∧ ((p5 → p4) ∨ ((p5 → (p2 → (p5 → ((True ∨ (p4 ∨ (p2 ∨ (p2 ∧ p3)))) → p2)))) → p5))) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3983342244408289926098495609 : (p1 ∨ (((True → (False ∨ p5)) ∨ ((True ∨ p3) → (p5 ∧ (False → (False → (p3 → p3)))))) → (((p1 ∧ (p1 ∧ True)) ∨ p1) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47491059230579321308158541047 : (((False ∨ (True ∧ ((((((p5 ∧ p5) ∨ ((p1 → True) → (p4 ∧ (p2 ∧ True)))) → False) → p5) → p1) ∨ (p1 ∧ p5)))) ∨ (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219819862246989008956834865448 : ((p3 → ((p5 ∨ p3) ∧ p4)) → ((p3 ∧ ((((p1 ∨ p4) → ((False ∧ (p4 → False)) → p3)) → p4) → p2)) ∨ ((True ∧ (p5 ∧ False)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304120990482381039382852816631 : (p1 ∨ ((p4 → ((p4 → (((p1 → p3) ∧ p3) ∨ (False ∧ False))) ∨ (p4 → ((p2 ∨ ((p2 ∧ p5) ∧ p2)) ∨ (p2 → (True ∨ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184131136499806593928580468298 : (((p2 ∧ ((((p5 ∨ p3) ∧ p1) ∨ (p2 ∧ p2)) ∨ p1)) ∨ False) ∨ (p4 → (((p1 ∧ (True ∧ (p5 → p5))) → (p5 ∨ (False → p4))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157548903518882412166482560152 : ((((p1 ∨ ((((p5 ∧ False) ∧ (p1 → p2)) → p5) → (p5 ∨ (p4 ∧ True)))) → p1) → (p5 ∧ p1)) ∨ (True ∨ ((True ∧ p3) → (False ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37074829681595589261468602435 : (((((((((p3 → (p5 ∧ (p2 → False))) ∨ ((p3 ∨ p5) → (p4 ∧ (p2 ∧ False)))) ∨ p1) ∨ (True ∧ p1)) ∨ p4) ∨ False) ∧ p4) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781867435509773969539811477570 : (((p2 ∨ (p1 → ((((p3 ∨ ((p1 ∨ p5) ∨ True)) ∧ (p1 → ((p5 ∨ (p5 ∨ ((False → p4) ∨ p2))) → (True → p4)))) ∧ True) → p4))) ∨ False) ∧ True) := by
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
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p5 ∨ (p5 ∨ ((False → p4) ∨ p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h18 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h19 := h6 h18
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h20 : (p5 ∨ (p5 ∨ ((False → p4) ∨ p2))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h22 := h19 h20
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h24 := h22 h23
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h26 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h27 := h6 h26
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h28 : (p5 ∨ (p5 ∨ ((False → p4) ∨ p2))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h29 := h27 h28
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h30 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h31 := h29 h30
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h32 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h33 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h34 := h6 h33
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h35 : (p5 ∨ (p5 ∨ ((False → p4) ∨ p2))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h36
        -- False on the left can always be used.
        apply False.elim h36
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h37 := h34 h35
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h38 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h39 := h37 h38
      -- One of the premise coincides with the conclusion.
      exact h39
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207227323747771354503760891705 : (((((False ∧ p5) ∨ p1) ∨ p4) ∨ p2) → ((p3 → (p5 ∨ False)) ∨ (((False ∧ p5) → (p4 ∨ p1)) ∨ (p5 → ((p2 → (p3 ∨ p3)) ∨ True))))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- False on the left can always be used.
        apply False.elim h5
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37622945176303760166951088262 : (((((((((False → (False ∧ ((True → p3) ∧ (p1 ∧ p1)))) → ((p1 ∧ (p3 → p5)) ∨ True)) ∧ True) ∨ p3) ∧ p5) ∨ p1) → p3) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173230738735861126921855653490 : ((True → ((((True → p1) → ((((p3 ∧ True) ∨ p4) ∨ p1) ∨ p5)) ∧ p3) → p1)) ∨ ((((p4 ∨ p2) → (p1 ∧ (p3 ∧ False))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615247504052949006639528787848 : (((((p4 ∨ ((p4 ∨ p3) → (False ∧ (((p3 → (p5 ∨ p2)) ∨ p5) ∨ (p5 ∧ p4))))) ∧ ((p5 ∨ False) → (p4 → (p4 ∧ p2)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192289642485381236774014949282 : ((((p4 → False) ∨ (p3 → ((p3 ∨ False) ∧ p2))) ∧ p5) → (((p2 ∨ p1) ∨ (p1 → (((p1 ∧ p4) ∨ (True ∨ True)) ∨ p1))) ∧ (p4 → p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47199534221863298891335328683 : (((((p1 ∨ ((p4 → p4) ∧ (p1 → p3))) ∧ (True ∨ (p4 ∧ p4))) → (False ∧ ((p5 ∧ (False ∧ (p4 → p3))) → False))) ∨ (True → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178529698744577144802749825805 : ((((False ∨ (p1 ∧ p3)) → (True ∨ (p2 ∨ p1))) → ((p1 ∨ p4) ∨ p5)) ∨ ((p2 ∨ ((False → p2) ∨ p1)) ∨ (p2 → (p1 → (p3 ∨ p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698902903001795039273632074 : (((True → (((p4 ∨ ((p5 ∧ (p4 ∧ True)) ∧ p1)) ∧ p2) ∨ p3)) → (((p4 ∨ p4) ∨ ((p5 ∨ (p2 → False)) → p4)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115073386010287040779277593154 : ((((p3 ∧ False) ∨ ((p4 → p1) → (((False ∧ p3) ∨ True) → p5))) ∨ ((p4 ∨ ((False → p3) → (False ∨ (False → False)))) ∨ p4)) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316854321617552734018765730073 : (p3 ∨ (p1 → ((False ∧ (((p5 ∧ (((p2 ∨ p3) ∧ p4) ∧ ((False ∧ p1) ∨ p1))) ∨ (p4 → (p5 → True))) ∧ (p2 ∨ (p3 ∧ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244879393250101866999842099330 : ((p1 ∧ p2) ∨ ((p5 ∨ ((p5 ∧ (p1 ∨ (p4 ∧ ((True → p4) → p1)))) ∨ p4)) ∨ (False → (p3 ∧ ((False → (p5 → True)) ∨ (p3 → False)))))) := by
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
theorem thm_5_vars_49967262253089651748453259791 : ((((p3 → ((((p1 ∨ p1) ∧ (p5 ∧ p5)) ∧ (p5 → p5)) → (True → False))) ∧ ((p2 ∨ p5) ∧ p4)) ∧ (p4 ∨ ((p4 → p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133992730365100035139257152067 : ((((((False → (((p5 ∨ False) ∧ (False → p2)) ∧ False)) ∨ p3) ∧ (True ∧ ((p2 ∨ p5) ∧ (p2 → p5)))) ∧ p4) ∨ p3) ∨ (p2 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57818567757456131229912728881 : (((p3 ∧ (p2 ∨ p5)) → ((p4 ∧ (p1 ∨ (p4 ∧ (True ∧ (False ∧ False))))) ∨ ((p2 ∧ (True ∨ ((p4 ∨ p4) ∨ p4))) ∨ (p5 → p3)))) ∨ p5) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913499245711403377419277125654 : ((((p3 ∨ ((p5 → (((True ∨ p3) ∨ (p3 ∨ ((p2 ∧ p4) ∧ (p3 → True)))) ∨ True)) ∨ p4)) → ((True ∨ ((True → p5) ∨ p1)) ∧ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p5 → (((True ∨ p3) ∨ (p3 ∨ ((p2 ∧ p4) ∧ (p3 → True)))) ∨ True)) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593628556659761753020328571154 : (((((((((p4 ∧ (p2 → False)) → (p3 → (True → (p4 ∨ (p5 ∧ p1))))) → p1) ∧ p2) ∨ p4) ∧ (((p2 ∧ p1) ∨ p4) → p1)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134361953609114803988107321801 : (((p1 ∨ (((p2 ∨ (p2 ∨ p1)) ∨ (True → (p4 ∧ ((p4 ∧ True) ∨ ((False → (p3 ∨ p2)) → p1))))) ∨ p4)) ∨ True) ∨ ((p1 → p1) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342858222420217344862628007851 : (p2 → (((p1 ∨ (False ∧ False)) ∧ (False ∨ p1)) ∨ (((p1 ∧ ((p2 → p2) ∧ False)) → (p1 → (False → p5))) ∨ (((p2 ∨ p5) ∧ False) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189985962305120118998864400831 : ((p5 → (((True → p1) ∨ (p1 ∨ True)) ∨ (True ∨ p3))) ∧ (((p4 → (False ∨ (p1 ∧ (p2 ∧ p2)))) ∨ (p4 ∨ (p3 → p2))) ∨ (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114382008606900214976560730421 : ((((p5 ∨ (True ∧ ((p1 ∨ ((p5 ∧ (False → p4)) ∨ (p1 ∧ (False ∧ False)))) → p5))) → p2) ∨ ((True ∨ (p4 → p4)) ∨ False)) ∨ (p5 ∨ False)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191750873573984280426063814084 : ((False ∨ (p5 ∧ ((p3 → (False ∧ (p4 ∧ p1))) → p2))) ∨ ((p3 ∨ (p5 ∨ ((p2 → p3) ∧ p2))) → (p3 → ((p3 ∨ True) ∨ (p2 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119108933521634865343815706349 : ((p1 → ((p2 ∧ p5) ∧ ((((p4 → p3) → False) ∧ (((p2 ∧ p3) → (p3 → (False ∨ p4))) ∧ ((p4 ∨ p2) → p4))) ∧ p5))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149587898990591888414156424968 : ((p3 ∧ (((((p1 ∧ p3) ∧ p5) ∨ ((p1 → p3) → ((p3 → ((p5 ∧ p3) ∧ p1)) ∧ False))) ∨ p4) → p4)) ∨ ((p4 → p4) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124032444009280388946371958718 : (((((p3 ∨ ((True ∨ p2) ∧ (p5 ∨ p1))) ∧ (p2 ∨ p3)) ∨ p2) → (((p5 ∨ (p3 ∧ False)) → p4) ∧ ((p3 ∧ p4) ∨ p5))) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65938544070738797266989450837 : ((p4 ∨ (False ∨ (p1 → ((p5 ∨ (((p4 ∧ (((p1 ∧ p4) ∧ (p3 ∨ (((p5 ∧ p4) → True) → p4))) ∨ p2)) ∨ p2) ∧ p3)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253114904595962347845290444214 : ((True ∧ p5) → (((((p2 ∨ (True ∧ ((True ∨ (p4 → (((p4 → False) ∨ (False ∨ p4)) ∨ p4))) ∧ (True ∨ p4)))) → p4) ∧ p5) ∨ p5) ∨ True)) := by
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
theorem thm_5_vars_867462296639221910692156081 : ((p5 ∨ (((((((p2 ∧ True) ∨ ((True → p5) ∧ (p1 ∨ p2))) ∨ True) ∨ ((p4 → p2) ∨ p4)) ∧ True) ∨ (p5 → p5)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301048331971906468386042115380 : (False ∨ (((((True ∨ False) ∨ ((p5 ∨ p3) ∧ p5)) ∨ True) → False) ∨ (False → (p1 ∨ ((p5 ∧ ((False ∨ p1) ∧ False)) → ((True → p2) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40926918644322065248215405557 : ((((((((p2 ∧ p4) ∨ ((p2 ∧ (p1 ∨ (False ∧ p5))) → ((p2 → (p3 → p5)) → p2))) ∨ p5) → False) ∧ p3) ∨ (p1 → True)) ∨ p3) ∨ p4) := by
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
theorem thm_5_vars_707832822489636109826099741033 : ((((p1 ∧ (p3 ∨ (p3 ∧ ((p4 ∧ p5) ∨ False)))) ∨ ((True ∨ (p1 ∨ p1)) → ((p4 ∧ p4) → (True → ((p1 ∧ p4) ∨ (p5 → True)))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614116454100180615642826041561 : (((((p2 → (((p4 → (False ∨ False)) ∨ ((p5 ∨ (p3 ∨ (p3 → False))) ∨ ((True ∨ False) ∧ True))) → p4)) ∨ (False ∨ (p3 ∧ True))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_57062262193889756546984432835 : (((p4 → (p3 → p5)) ∧ ((True ∧ ((p3 ∧ p5) ∧ (p5 ∨ ((p2 → p4) ∨ (((p5 → (p4 ∧ True)) → p4) ∨ (False → p2)))))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217125705373156108301746753720 : ((((p4 ∨ p3) ∨ False) ∨ p3) → ((p5 ∧ False) ∨ (((p2 → p4) ∨ p2) → (p4 → (((((p1 → p3) ∧ p2) → (p3 ∨ p4)) ∨ p1) ∨ p2))))) := by
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
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
          exact h6
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h16
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h25
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701926316699808518548837464942 : ((((p2 ∨ (((p3 ∨ p5) ∨ ((p3 → p2) ∨ p5)) ∧ False)) ∧ ((p5 → ((((((False ∧ False) → True) ∨ p5) ∧ p1) ∧ False) ∨ True)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197711455381990420933754981250 : ((((p1 ∧ False) ∧ p1) ∧ ((p3 ∨ True) ∨ False)) ∨ (((((((((p2 → p3) ∨ p4) → p4) ∧ p4) ∧ (p2 ∨ p5)) → p2) → True) → False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p2 → p3) ∨ p4) → p4) ∧ p4) ∧ (p2 ∨ p5)) → p2) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248712933499227799109667394269 : ((p3 ∨ p2) ∨ (((True → False) ∧ p1) ∨ ((((p3 → True) ∨ (True ∧ (((p1 ∧ p1) ∧ (p3 ∧ p5)) ∧ (p1 → p5)))) → (p5 ∨ False)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → True) ∨ (True ∧ (((p1 ∧ p1) ∧ (p3 ∧ p5)) ∧ (p1 → p5)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37362427285915475629532538684 : (((((((p5 ∧ True) ∨ p4) ∧ (p4 ∧ (((True → ((p4 → False) ∨ False)) → False) ∧ (p5 → (p3 → (p1 ∧ p3)))))) ∨ p2) ∨ True) ∧ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172542315944883891556927598655 : ((((True → p1) ∧ p1) ∨ (((False → ((p4 ∨ p1) → (p5 → False))) → p4) ∨ False)) ∨ (((p1 → (p2 → ((True ∧ False) ∨ True))) ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54580676007768543283924408149 : (((p2 ∨ ((True → p4) ∨ (p1 ∧ (p5 → True)))) ∨ ((p2 → p4) ∧ ((False ∨ p4) ∨ (False ∨ ((False ∨ (p5 → p3)) ∨ (p2 → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199958751582912174484185165747 : (((p5 ∨ (False → (p2 ∨ p5))) ∨ (p5 ∧ p5)) → (p1 → (((p5 ∨ (((True ∨ p3) → (p2 ∧ p3)) → (False ∧ p5))) ∨ True) ∨ (p2 ∧ p1)))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119205289059238263384046421617 : ((p2 → ((p1 ∧ (p3 → (True ∨ (((True ∨ (False ∨ p3)) → p5) → (p3 ∨ p1))))) → (((False ∨ (p1 → False)) ∧ p4) ∨ p4))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230872650069582666767983258271 : (((p1 ∧ p5) ∨ p3) → ((True ∧ ((((((p4 → (p3 ∨ p5)) ∨ (p2 ∨ p4)) ∨ p5) ∧ ((p2 ∧ False) ∨ p2)) ∧ False) ∨ (p1 → True))) ∨ p2)) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151153220197170928339937401321 : (((((((p4 → (p1 → (p1 → True))) → p1) ∨ (p1 ∨ (p2 ∧ p1))) ∨ True) ∨ (p3 → (p4 → p5))) → False) → ((p1 → (False ∨ p4)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((p4 → (p1 → (p1 → True))) → p1) ∨ (p1 ∨ (p2 ∧ p1))) ∨ True) ∨ (p3 → (p4 → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((((p4 → (p1 → (p1 → True))) → p1) ∨ (p1 ∨ (p2 ∧ p1))) ∨ True) ∨ (p3 → (p4 → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184898308339271281391199704827 : ((((p5 ∧ p3) ∧ p2) ∨ ((((p5 ∧ p4) → False) → False) ∨ p3)) ∨ ((p1 → (True ∨ (p5 ∧ ((p2 ∨ p5) ∨ p1)))) ∨ (p5 ∨ (p5 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57128975354045015765116017763 : ((((True → p4) ∧ p5) ∨ (p3 ∨ ((p1 ∨ p1) ∨ ((p5 ∧ (p4 → p1)) ∨ ((True ∧ p4) ∧ (False ∨ ((p4 ∧ (p4 ∧ False)) → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18121679144923883934866013833 : (((p3 → (((((p2 ∧ ((False ∨ p4) ∨ (False ∧ p1))) ∧ p4) ∧ p3) ∨ ((p3 → p2) ∨ True)) ∨ p2)) ∨ ((p3 ∨ (p4 → p1)) ∧ False)) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4208919072088527527883303648 : (p5 ∨ ((p5 ∧ (((p1 ∨ p2) → (p4 ∧ p1)) → ((p4 ∧ p3) ∧ ((p5 ∧ (p4 ∨ ((True ∨ True) → p1))) → (p2 → p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706999586303217899289823766163 : (((((p1 ∧ (p3 ∨ (p5 ∨ (p5 ∧ True)))) ∨ False) ∨ ((((True → ((p2 → p2) ∧ ((False ∧ p3) ∨ p4))) → False) → False) ∨ (p3 → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152011566673907737121708837503 : (((p4 ∨ (((p4 → ((p1 ∧ p2) → p5)) ∧ (p2 ∨ p5)) ∨ False)) → (((p2 ∧ p4) ∨ (True ∨ p2)) → p2)) → (((p4 ∨ p5) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601056102045514080720918712836 : ((((p1 ∧ ((False → (p3 ∧ p2)) → ((p1 ∧ p3) ∧ (True ∨ (((p5 → p4) → ((p2 → p5) → ((p3 ∨ p2) → True))) → p2))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84849627232171813155418175879 : (((p2 → ((((False ∨ (p2 ∨ p3)) ∨ (False → False)) ∧ False) ∧ (False ∧ p4))) ∧ ((((True → p3) ∧ (False ∨ p2)) ∨ (True → True)) → p2)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((True → p3) ∧ (False ∨ p2)) ∨ (True → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_477542135155244768808124248274 : (((((p5 ∧ ((((p3 ∨ True) ∨ p5) → p4) → p1)) → p2) → (p2 → (((p4 → (((p2 ∨ p3) → p4) ∧ (True ∨ p5))) ∧ p2) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247595870361441937476519996825 : ((False ∨ p5) ∨ ((((((p3 → (p2 ∨ ((p1 → p2) ∨ p3))) → p2) ∨ (p2 ∨ (p4 ∧ p5))) ∨ p4) ∧ (p1 ∧ (p1 → (p5 ∧ False)))) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      let h6 := h3.left
      let h7 := h3.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h3.left
        let h14 := h3.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h3.left
        let h22 := h3.right
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h23 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h24 := h22 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- False on the left can always be used.
        apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h3.left
    let h28 := h3.right
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h29 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h30 := h28 h29
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56588068444404689480259979371 : (((p2 → ((False ∨ p5) ∨ p1)) → ((p1 ∧ (((((p2 → (p3 → True)) → p3) → True) → (((p2 ∧ p1) ∧ True) → p4)) → False)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111850365988194058372362572518 : (((((((True ∧ p2) ∧ (p4 → False)) → (p3 ∧ p5)) → (p4 ∨ (p3 → ((p4 ∧ p1) ∧ True)))) → ((p5 → True) → p2)) ∨ True) ∨ (p1 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198367831478436308704083051349 : ((p3 ∧ ((p2 ∨ (p3 ∨ (p4 → False))) ∧ p5)) ∨ (((p5 ∨ (True → ((p2 ∨ p5) ∨ p2))) → p4) ∨ (p2 ∨ ((p5 ∧ True) → (p1 → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136557422362109225379908746586 : ((((p2 ∨ False) ∨ p2) ∨ (((True ∨ ((((True ∧ (p5 → p3)) → p5) → False) ∨ (p1 → True))) ∧ (p1 ∨ p3)) ∧ False)) ∨ ((p5 ∧ p3) → p5)) := by
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
theorem thm_5_vars_219077789066450750005650719365 : ((p5 ∧ (p1 → (p4 ∧ False))) → ((((p1 ∨ ((p5 → (True → p4)) ∨ (p3 → (p1 ∧ (p1 ∨ False))))) ∧ (True ∨ (p2 ∧ p4))) ∧ False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804930496643377702204125806441 : (((p3 → ((p5 ∨ False) ∨ ((p1 ∨ p1) → (p5 → ((p4 → (p1 ∨ (p3 → (p4 ∧ True)))) → ((p4 ∨ (p5 → p1)) → (p2 ∨ p1))))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602807131510898316023914379977 : ((((False ∨ (p5 → (((p3 ∨ (True ∨ (p5 ∨ False))) → p3) ∨ (((p2 → p3) ∨ p2) ∨ (p2 → ((False ∨ p2) ∨ (False ∧ False))))))) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301518445520506871728191734305 : (False ∨ (((p1 ∧ p1) ∧ p1) ∨ (((False → True) → (p5 ∧ p1)) → ((p3 → (((p4 ∧ p5) → p1) ∨ (p4 → (p5 → (p3 ∧ p1))))) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h10
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37713059408286855824590249352 : (((((((p5 → (False ∧ False)) ∧ False) → ((p2 ∧ p3) ∨ (((p4 ∨ p4) ∧ p4) → p3))) ∨ (((p2 ∨ p5) → False) ∧ p2)) → p5) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122664617901334427438175869856 : ((((((p4 ∧ ((p4 ∨ p3) ∨ True)) ∨ True) ∨ ((False ∨ p2) ∨ (True → p3))) ∨ (((p5 → p3) → p4) ∧ True)) → (False ∨ False)) → (p1 ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ ((p4 ∨ p3) ∨ True)) ∨ True) ∨ ((False ∨ p2) ∨ (True → p3))) ∨ (((p5 → p3) → p4) ∧ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((((p4 ∧ ((p4 ∨ p3) ∨ True)) ∨ True) ∨ ((False ∨ p2) ∨ (True → p3))) ∨ (((p5 → p3) → p4) ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207154363570534789196501982989 : (((p2 → (p1 ∧ (p3 ∨ p3))) ∧ p3) → ((p3 → (True ∧ (p4 ∨ ((False ∨ (True ∨ (True → p2))) ∨ True)))) → ((p1 ∨ p3) ∧ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351326968395130223104857037395 : (p4 → ((p1 ∨ ((p2 ∨ (p4 ∨ (((p1 ∨ ((p5 ∧ p1) → p5)) → p3) → (((p5 ∨ p5) → p1) ∨ False)))) ∨ p1)) → (p3 → (p5 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21524603485029298400888771756 : ((((p3 → True) → ((p1 → ((p5 → p1) ∧ False)) → p3)) ∨ (False → (False ∧ ((((p5 ∨ (False → (True → True))) → p3) ∨ p3) ∧ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198582199971529907208963059995 : ((p1 ∨ (p3 ∨ ((p2 ∧ (p5 ∧ False)) ∧ p2))) ∨ ((p1 ∧ ((p5 ∨ (p4 → (False → True))) ∧ p3)) ∨ ((True ∧ p3) → (p4 → (True ∨ p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709215490088847278470845548476 : (((((p2 → p4) ∧ ((p1 ∧ (True → False)) ∧ True)) → ((p5 ∨ (p1 → (p1 ∧ False))) ∧ ((p4 → ((p4 ∨ p4) → (True → p3))) ∨ p3))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50791863881008191625840548105 : (((True → ((((False → (p5 → p2)) ∧ (p4 ∨ p1)) ∧ ((True ∧ ((p1 → p2) ∨ p3)) → p1)) ∧ True)) → ((True ∧ p1) ∧ (p3 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192297134046992657753583682804 : ((((False → p4) → ((p4 ∧ (p5 → p2)) ∧ True)) ∧ p1) → (p5 ∨ (((True → p2) ∨ p3) → (p1 → (((p3 → p1) → (p2 ∨ p2)) ∨ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h13
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118222327469331022772184709229 : ((p1 ∨ (((((False ∧ (p2 ∨ False)) ∧ (False → (p2 → p4))) ∧ p1) ∧ (p3 ∧ (((True ∧ (p1 → False)) ∧ p3) ∨ True))) ∨ p5)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356908750640061722006000777079 : (p5 → (((p4 → p2) → (True → p3)) → (p5 ∧ ((p4 ∧ (p3 ∧ (False ∨ (p1 ∧ p5)))) ∨ ((p4 ∧ ((p2 ∧ (p3 ∨ p2)) ∧ True)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111636021502805824871791525056 : (((((p4 ∨ ((p5 → p2) ∧ (((p3 ∨ p2) ∧ p2) ∧ (True → True)))) → (False ∨ (p2 → ((False ∨ p5) ∨ p5)))) ∨ True) ∨ p5) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173052470757122470043424326840 : ((False ∨ (((p2 → True) ∨ (p5 ∧ ((p3 ∧ True) ∧ ((p4 ∧ p2) → p1)))) → p1)) ∨ (p3 ∨ (((False ∧ p4) ∧ p1) → ((p4 ∨ p1) ∨ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307499703571991647568865123583 : (p1 ∨ (True → ((((p1 ∧ False) → (((p2 ∨ (((p3 ∧ False) ∨ False) ∧ ((False ∨ p2) → False))) → p3) ∧ p1)) → False) ∨ ((p2 → p2) ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174786929202037043214467028437 : (((p1 ∨ p4) ∧ (((p2 ∨ (((p3 → False) ∨ (p2 ∧ p1)) → p1)) → p4) ∨ p2)) → ((p1 ∨ ((p4 → False) → (p3 ∨ True))) ∧ (p2 ∨ True))) := by
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
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261637838755700936044587399695 : ((p5 → p5) → ((((((p1 ∨ p5) ∨ p2) ∧ p2) ∨ p2) ∨ (True ∨ ((p2 ∨ False) ∧ (p1 ∨ p1)))) ∨ (((p4 → False) ∨ (p4 → p5)) ∧ p2))) := by
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
theorem thm_5_vars_251551477021225424818275101561 : ((p3 → False) ∨ (((((False ∨ ((p5 → (p3 ∨ False)) ∨ False)) ∨ ((True → p4) → (True ∧ True))) ∨ (p2 ∧ p5)) ∨ False) ∧ ((False ∧ p3) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231432845026694261460890688456 : (((p2 → False) ∨ False) → ((False ∧ ((False → (False ∧ p1)) → (False ∧ p4))) ∨ (((True → (False → (p3 ∨ False))) ∧ p2) → (p3 ∧ (p3 ∧ False))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65942934192447515432199027106 : ((p4 ∨ (p1 ∨ ((p2 → False) → ((((p5 ∨ (p2 ∧ ((p4 → (p2 ∨ p1)) → p1))) ∧ True) → (p4 ∨ ((False → p3) ∧ False))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67777972187479641409488369252 : ((p2 → ((p5 ∧ (((p2 ∧ (p2 → True)) → p3) ∨ (p2 ∧ (((p2 ∨ (p3 ∧ p1)) ∧ (False ∧ p3)) ∧ ((p1 → p3) ∧ p3))))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714424573514421288388932859209 : (((((p2 ∧ (p1 → True)) → (p3 → p2)) → (((p5 ∧ p4) ∧ (((p5 ∧ False) → (((p1 ∨ p2) ∧ False) → p3)) → (p3 ∧ True))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



