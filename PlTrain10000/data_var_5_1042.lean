variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760716022885763062999984599783 : (((p2 ∧ (False ∨ ((((p2 ∧ p2) → (p5 ∨ (((False → (((p5 ∧ False) → p3) ∧ p3)) ∨ p3) ∨ (p1 ∧ p4)))) → (p1 ∧ p3)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184370062062504630505372718739 : (((p4 ∨ (((((p2 → p5) → p2) ∨ p2) ∨ p3) → p3)) → p2) ∨ ((False ∧ (p5 → p4)) → (((((p3 → False) ∧ False) ∧ p2) ∧ p4) ∨ p3))) := by
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
theorem thm_5_vars_199770123865681049886300309276 : (((p2 → (False ∨ ((False ∧ True) ∨ p5))) → p1) → ((p2 ∨ (p1 ∨ False)) → (((p3 ∨ (p4 ∨ (p5 ∧ p1))) → (p1 ∨ (p2 → True))) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h25
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185561273055610561125897097392 : ((p4 ∨ ((p1 → (p1 → p1)) ∧ ((p5 ∨ p5) ∨ (p2 → p5)))) ∨ ((False ∨ (((p5 ∧ (True ∧ p1)) ∧ True) → ((p5 ∧ p1) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204931606288226875543216731084 : ((((False ∧ p2) → (p5 ∧ p4)) → p1) ∨ (True → ((p5 ∧ ((False → p3) ∧ (p3 ∨ (((p2 ∧ p3) → True) ∧ ((True ∧ p1) ∨ p2))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72139114420459631461718504279 : (((True → (p5 ∧ (((p1 ∨ ((p5 ∧ ((False ∧ (p1 ∨ p4)) → p4)) ∧ (p4 → (p1 ∨ (p3 ∨ p5))))) ∨ p4) ∧ (True ∧ False)))) ∧ p5) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757394065106995709729866928727 : (((p1 ∧ ((p4 ∨ p4) → (False ∨ ((p1 ∧ (((p3 ∧ ((((p2 → p2) ∧ (False ∨ p1)) → True) ∨ p5)) ∧ False) ∨ p4)) ∧ (p3 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19158717948746761587067850264 : ((((False ∨ False) ∨ (p5 ∨ (((((p1 ∧ p2) → ((True ∧ True) → p3)) → p3) → p4) ∧ True))) → ((((False ∧ p4) → p4) ∧ p3) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219107527637306298872171582200 : ((True ∨ ((True ∧ p1) → p4)) → (((p5 → True) ∨ False) → (((p1 ∨ (p1 ∧ ((True ∧ (p4 → p4)) ∧ (p4 ∨ p5)))) → p5) ∨ (False → p5)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354612718500668650379941884058 : (p5 → ((((((p2 ∧ p4) ∨ True) ∨ ((((False ∨ p3) ∧ (p1 ∨ (p5 ∨ True))) ∨ p3) ∨ (p4 → p4))) → ((p1 → p5) → p4)) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206008416280462676330639685833 : ((p2 ∧ (((p5 ∨ True) ∧ p4) ∧ p2)) ∨ (((p5 ∨ p3) ∨ True) ∨ (((p3 → (p2 ∨ False)) → (((p1 ∧ True) → False) ∨ (p1 ∧ False))) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147943947988132149728780543029 : ((((p5 ∧ p4) ∨ (p5 ∧ ((p5 → p2) ∧ (p5 ∨ (False ∨ (p1 ∨ (p1 → (p1 → p5)))))))) ∧ (p4 ∧ p3)) ∨ (((p2 ∧ False) → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_447943679493324793857501639349 : ((((p4 ∨ ((((p5 → (True ∧ (p3 ∨ (p5 ∨ p4)))) → True) ∨ ((p4 → ((p5 → p3) ∨ False)) ∨ True)) → p4)) → ((p1 ∧ p1) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p5 → (True ∧ (p3 ∨ (p5 ∨ p4)))) → True) ∨ ((p4 → ((p5 → p3) ∨ False)) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703792560853657418106525930151 : (((((p4 → ((p5 → p2) ∨ (p1 → (p2 → False)))) ∧ p2) → ((p3 → p1) ∨ (p2 ∨ (((p5 → ((False → p2) → False)) ∨ p5) → True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231890841879457563639101715026 : (((True ∨ p4) → p3) → ((True ∧ p1) ∨ (((False ∨ p1) ∨ (True ∨ ((p5 → True) ∧ p1))) ∧ ((((True ∨ True) → (p5 ∨ p2)) ∨ True) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_147193251218295383222982841866 : (((p5 ∨ (((p4 → (p2 ∨ (p4 → (p2 → ((p3 ∨ (p5 ∧ (False ∨ False))) ∧ p2))))) ∨ p1) → p1)) ∧ p3) ∨ ((False ∧ (p4 ∧ p1)) → p3)) := by
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
theorem thm_5_vars_29790783282372406672272713 : ((p4 ∧ (((p5 → (p4 ∨ ((p4 ∨ True) → True))) ∧ (True → p1)) → p2)) → (False ∨ (((p2 → p3) → p1) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_48533002731307391990939211814 : ((((False ∨ (p4 ∨ ((((((True → p3) ∧ (p4 → p1)) ∨ p1) ∨ p1) ∨ (False ∨ False)) ∨ (p4 → p4)))) ∨ True) ∧ (p5 ∨ (p3 → p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_379658048258280019442005285305 : ((((((((((p3 ∧ True) ∨ (p2 ∧ ((p2 ∧ p5) ∨ p4))) ∧ True) ∨ (p4 ∨ (p5 ∧ p3))) → (False ∨ (p4 ∧ p4))) ∧ p1) ∧ p4) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_178518194691302189496786583470 : (((((((p2 → False) ∨ p3) ∨ p1) → False) → True) → (p1 ∧ (p4 ∧ p1))) ∨ (((p5 ∨ (p1 ∨ p5)) → (True ∨ True)) ∨ (True ∨ (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156823465938244488493365013444 : (((p4 ∨ (p4 ∧ (((p5 ∧ ((p5 ∨ False) ∧ p4)) ∧ (p1 ∨ p1)) ∧ ((p5 ∨ p1) ∧ p2)))) ∧ True) ∨ ((p4 ∨ ((p3 ∧ False) ∨ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_513491704686152037698480685274 : ((((False ∨ False) ∨ ((p1 ∧ True) ∨ (p3 ∨ (((p2 ∨ (p4 ∨ (False → ((p4 → p4) → (True ∨ p1))))) ∨ True) ∨ (p5 ∨ (True ∨ p4)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41836413392851673854633945038 : ((((p4 ∧ (p2 → False)) ∧ ((p5 → p1) → (p1 ∧ (((p4 → p3) ∧ (((p2 → p4) ∧ p1) → p4)) → (p4 ∧ (p2 → p4)))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764050114482112278160173713474 : (((p3 ∧ (p2 → ((((p3 → ((((p4 ∧ (True ∨ p3)) ∧ True) ∧ p2) → p1)) ∨ p2) → ((p1 ∧ (True ∨ p3)) ∨ (p2 ∧ False))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217057228062419187450070405552 : ((((True → p5) ∧ p4) ∨ p1) → (((p1 ∧ (((((p2 ∧ False) → (p5 → (p3 → p1))) ∨ p5) → True) → p2)) ∧ (p1 ∨ p5)) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82666151319762414224565149014 : ((((p2 → ((((False → p2) ∨ ((p4 ∨ False) → p1)) ∧ (p5 ∨ p4)) ∨ p2)) → ((True → p4) ∧ False)) ∨ (True → (False ∧ (True ∨ p3)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p2 → ((((False → p2) ∨ ((p4 ∨ False) → p1)) ∧ (p5 ∨ p4)) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356661991908392579876678581394 : (p5 → (((True ∧ p1) ∨ ((p5 ∨ False) → (p1 ∨ p2))) → ((((True → p1) → p5) → p2) → ((((p2 ∨ p5) → (p3 ∧ True)) ∨ p5) ∨ p2)))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50930768872140713354277438057 : ((((((True ∧ ((True → p3) ∧ ((p2 ∧ p1) ∧ False))) → False) → False) → (p5 ∨ (p2 → p5))) ∧ (((p1 ∨ (p5 ∧ p1)) ∧ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264166485508664465315852756834 : (True ∧ ((((False ∨ True) ∨ p4) → ((p2 → False) ∨ p4)) ∨ ((p1 → (p5 → ((p3 → (((p4 → p4) → False) ∨ True)) ∧ p5))) ∨ (True → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52452385843038709284566665989 : (((p4 ∧ (((((p3 → p5) ∨ (True ∨ True)) ∧ p2) ∧ True) ∨ (p3 → p3))) ∧ ((p4 ∨ ((True → p3) ∨ (p3 → False))) ∨ (p1 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134110107031722362315150561929 : (((((((p1 → p1) ∨ p4) ∧ (False ∨ p4)) ∨ ((((p4 ∧ True) → p3) ∧ p5) ∧ (p2 → p2))) ∧ (p2 ∨ True)) ∨ p1) ∨ ((p2 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59501767848807618803054552421 : (((p2 → False) ∨ ((((((p2 ∨ (((p3 ∧ (p3 ∧ True)) → p3) ∧ p2)) ∧ True) ∧ p3) → (False ∧ p5)) ∨ (p2 → (p5 ∧ p3))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115990250174133643257448282642 : (((((False ∧ p4) ∨ p4) → False) → ((True ∧ ((True ∧ p2) ∨ (((((p3 ∨ (p5 → p5)) → p1) → p1) ∨ p1) ∧ p1))) ∨ True)) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780408552081915978952264726815 : (((p2 ∨ ((p5 ∧ (((((p3 ∧ ((p1 → p4) → True)) → p4) → p4) → p1) ∧ (p2 → p4))) ∨ (False → (p4 ∧ ((False ∧ p3) → p4))))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148439750811234455167572111809 : (((p5 ∨ ((p4 ∨ p2) ∧ ((False → p2) ∨ (False ∨ ((p5 → p1) → False))))) → (p2 ∨ (p1 → (True ∧ p3)))) ∨ ((p4 → p2) → (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64254164177482034042158542055 : ((False ∨ (p3 ∨ (p4 ∧ ((False ∨ ((False ∨ p3) ∧ (p3 ∧ (p1 ∧ (p2 ∧ ((p4 ∨ (p4 ∧ ((True ∧ p3) ∧ p4))) ∨ p4)))))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40321897349335800426569130482 : (((((p3 → ((((p4 → (False ∨ p2)) ∧ (True ∨ (((p2 ∧ (True → p1)) ∧ True) ∧ p5))) ∧ (p4 → False)) ∧ p5)) ∧ p3) ∨ p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626714784490317351838375035663 : ((((p5 → ((False ∧ (p4 ∨ (False ∧ (((p5 → ((p5 ∨ True) ∧ (p2 → (True ∨ p2)))) ∧ (p3 ∨ p2)) ∧ (True → p4))))) ∨ True)) ∨ False) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207223783529795380786664822999 : (((((p4 ∨ p3) ∧ p4) ∨ p2) ∨ p4) → ((p2 ∨ (p5 → p3)) → (p3 → ((p5 ∨ (((p4 → p3) ∧ ((p3 → p5) ∧ p2)) ∧ True)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338368374693613322822306086325 : (p1 → (((p1 ∨ p3) → (p2 ∨ p2)) ∨ ((p3 ∧ p1) ∨ (True → (True → ((p4 ∨ (True ∨ ((p4 ∨ False) ∧ (p5 → (True ∧ p1))))) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190585396030857147113489266088 : ((((p1 ∧ True) ∧ (True ∧ (False → (True ∧ False)))) → p2) ∨ ((((p2 → False) ∨ True) → (False ∧ ((False ∧ p5) ∨ p4))) → (p4 ∨ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47550778475591947874523097344 : (((True → ((((((p4 ∧ False) → p4) ∨ p2) ∧ (False ∨ p4)) ∧ (p4 ∨ ((p1 ∨ ((p4 ∧ p2) ∧ p2)) ∧ False))) ∨ True)) ∨ (p2 ∧ False)) ∨ p3) := by
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
theorem thm_5_vars_174769013715549849552615341961 : (((p2 ∧ p4) ∧ ((p4 ∨ ((False ∨ (True ∨ (p3 → p1))) → p3)) ∧ (p2 → p5))) → ((p1 ∨ p4) ∧ (((p1 ∨ True) → (p5 ∧ True)) ∨ p4))) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h11.left
  let h15 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10525205352968566626069895597 : (((p3 → ((p2 → (False ∨ ((((p4 ∨ True) ∨ ((True → p5) → (p3 ∨ p1))) → (False ∧ (p1 ∧ False))) ∧ (p4 ∧ p5)))) ∨ p3)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_37743651779712762458631129059 : ((((((p1 → (p2 ∧ True)) → ((p1 ∧ p1) ∨ True)) → ((p5 ∨ (False ∨ (p4 → True))) → ((p4 ∨ False) ∧ (p1 → p1)))) → False) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46018159092858046313518411588 : ((((((p3 → (p2 → False)) → p1) → (((((p3 ∨ True) ∧ p5) ∨ p1) ∧ (False ∧ p1)) ∨ (p3 ∨ (p2 → p2)))) ∧ True) ∧ (p3 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587813325288823087500183832170 : (((((((p5 ∧ (p5 ∧ (True → ((p3 ∨ p1) ∧ (((((p1 → p5) ∨ False) ∧ p3) ∨ True) ∧ p4))))) ∨ p3) ∨ (True ∨ p4)) ∨ p1) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158141571842689879144533503433 : ((((p5 → p1) ∧ (p2 ∧ p2)) ∨ (p1 ∨ ((p2 ∨ (p1 ∧ (p2 ∨ p2))) ∧ (p5 → (p1 → p4))))) ∨ (False → ((True ∧ p1) → (p4 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348761791825993029890817646671 : (p3 → (False ∨ ((p5 ∨ p5) ∨ ((((p2 ∨ p3) ∧ ((True → p3) → ((p5 → (False ∧ ((p3 ∧ False) → (p4 ∨ p1)))) ∧ p3))) ∨ True) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_40513094822043514947759416558 : ((((p3 ∧ (p2 ∧ (((((p2 → p1) ∨ (p5 → p3)) → p1) ∨ (p3 ∧ False)) ∨ (p5 → ((p4 ∧ True) → (p4 ∨ p4)))))) ∨ True) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238175907347745753855032287136 : ((True ∨ p4) ∧ (((p5 → (((p3 ∧ ((p4 → (((p2 ∧ False) ∨ p5) ∧ p1)) → (((False → p5) → p3) ∧ True))) → p4) ∨ p5)) ∨ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231074134293753680602288322343 : (((False ∨ True) ∨ p1) → (p4 → ((((p1 ∧ (p3 → True)) ∧ False) ∧ p5) ∨ (((p2 ∨ (True ∧ ((True → p5) → True))) → (p1 ∨ p1)) ∨ True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600782730798732922915728470763 : ((((False ∧ ((p3 ∧ p3) ∧ ((((True ∨ False) ∧ False) ∨ (((False → p3) ∨ p2) ∧ (p5 ∧ ((p3 ∧ (False → p1)) → True)))) ∨ True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20295370082263931891791188711 : (((p2 ∧ (((p1 ∨ (p3 ∨ p2)) ∨ (p1 → p3)) ∨ ((p1 → p5) ∨ p2))) ∨ (p3 → ((p4 ∨ ((p4 → p4) ∧ (True ∨ False))) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204419157007800177488855256860 : (((p4 → ((p3 → p5) → False)) ∧ p3) ∨ (((p4 ∨ ((p4 ∧ p3) → True)) ∨ ((((p3 ∨ p3) ∨ p5) ∨ p2) ∨ ((p3 ∨ True) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217535665560922743523585395027 : ((((p4 → False) ∧ p1) → p3) → ((((p1 → (p4 ∨ p2)) ∨ (((p2 ∧ p5) → False) ∨ (p5 ∧ False))) ∧ p3) ∨ (False → (False → (p1 → False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358129378529082730524723012404 : (p5 → (p2 ∨ ((True → p1) ∨ ((p3 ∨ (p3 ∨ ((((p5 ∨ (p5 ∧ (((p2 → False) ∧ True) → p3))) → p2) → (p4 → p1)) → False))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60434896590182528737715632141 : (((p4 → p4) → (p4 → (((p2 ∨ (True → p5)) ∨ False) ∨ ((p1 ∨ ((p5 ∨ p5) → p4)) ∧ ((p4 → (p2 ∧ p4)) → (p2 ∧ p2)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98921442857543082435635617439 : ((True → ((p2 → ((False → p2) ∨ (p1 ∨ ((((p1 ∨ (p1 ∧ (p5 ∧ p1))) ∨ p2) → ((p4 → p2) ∨ p2)) ∧ p4)))) ∧ (True → False))) → False) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69172665358020359640377820157 : ((p5 → (((((p1 → (p3 → ((False ∧ p2) ∧ p5))) ∨ (True ∨ False)) ∨ (p1 ∨ p3)) ∧ p4) → (((p3 → False) → False) ∨ (False ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157114123731492387398167675566 : (((p5 → (False ∨ (p2 ∧ (((p4 → p4) ∨ False) ∧ ((p5 ∨ (p1 ∧ p2)) ∧ (p3 ∨ p3)))))) ∨ True) ∨ ((p1 ∨ False) ∨ ((p1 → True) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427575059705509550761260182338 : ((((((((True → ((False → (p5 ∧ (False → True))) ∧ False)) ∨ (p4 ∧ ((p1 ∧ p1) ∨ (p2 → True)))) ∧ p5) ∧ p1) ∨ p4) ∨ (False → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149073861161375676145041391948 : ((((p3 → False) ∨ p3) → ((p2 ∧ (False → p1)) ∨ (((p4 ∧ p1) ∨ ((p5 ∧ p4) ∧ (True ∧ p5))) → p5))) ∨ (False ∨ (p5 → (p1 ∨ p5)))) := by
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
theorem thm_5_vars_321580113795183514119728603681 : (p4 ∨ (p2 → (p1 ∨ (p3 ∨ ((((p5 ∨ (p4 ∧ False)) ∧ p5) ∨ ((((True → p3) ∧ (p1 → p4)) ∧ p2) ∨ (p2 ∧ p4))) ∨ (p2 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754429208234070602386593421765 : (((False ∧ ((False → p4) → (((False ∨ p4) ∨ p2) ∧ ((((p2 ∧ ((True ∨ False) ∨ True)) → (p1 → p3)) ∨ p2) → ((p5 ∨ True) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647249506788338899670030999193 : ((((p4 → ((p3 → (((p1 ∨ ((p5 ∧ False) → p1)) ∧ (p1 → ((((p4 ∨ p1) → p2) ∨ p1) ∧ p2))) ∨ (p3 ∨ p4))) ∧ True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42512564160062304895326700609 : (((False ∨ ((p3 ∨ p3) ∨ ((((((p3 → p2) → p1) ∨ True) ∧ p2) ∨ (p2 → (((p3 → (False ∧ p4)) → False) → p2))) ∨ p3))) ∨ p4) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114660430810254503155707198466 : ((((((p4 ∨ p4) → p1) → True) → ((p1 ∧ p2) → ((False ∧ p2) ∨ (p3 ∨ False)))) ∨ (((p1 → False) ∧ p4) ∧ (p5 ∨ p1))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666765333475365639461521651258 : (((((((p2 ∨ (p5 ∧ p1)) ∧ p3) ∨ (p5 ∨ p2)) ∧ ((p4 ∧ (((p5 ∨ p2) → (False ∧ p4)) ∨ True)) ∨ True)) ∧ (False → (p2 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656716029748179450798786063600 : (((((((p4 → (p5 ∨ True)) ∧ p1) ∧ False) ∨ ((((((True ∧ (True ∨ p2)) ∨ p3) ∧ p5) ∨ True) ∧ (False → True)) ∧ False)) ∨ (True → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_776904555166081326907095300897 : (((p1 ∨ ((p5 ∨ ((False ∧ ((True → p5) ∨ p4)) → (p5 ∧ ((p1 ∧ ((p3 ∨ (p2 ∨ (p2 → False))) ∨ (p4 ∨ p2))) → p1)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725341081962239435959217368193 : ((((p4 → (p2 ∧ True)) ∧ ((((((p5 ∧ (p5 → (p3 ∨ True))) ∨ (p2 → (p1 → ((p2 → p4) ∨ p2)))) → p4) ∨ True) ∨ p3) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52602335552224501460144407225 : (((((p3 → (p4 → p5)) ∧ (p5 ∨ p5)) → ((p2 ∧ False) ∧ (False ∨ True))) ∨ ((False → (p1 → (p1 ∧ True))) ∧ (p2 ∧ (p1 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206423993284491072251814505096 : ((p3 ∨ (p1 → ((p4 ∧ p3) ∨ False))) ∨ ((((p3 ∨ (p2 → True)) → (((((p4 ∧ True) → (p2 → False)) → p1) → p3) ∧ p2)) → p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780227769309308266988511529843 : (((p2 ∨ (((((p2 ∧ ((p1 ∨ ((True ∨ p3) ∨ False)) ∨ (p1 ∨ p4))) ∧ p2) ∧ (p3 → (p2 ∧ True))) ∧ p4) → (False ∨ (p1 → True)))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39204914926590740772213453853 : (((True ∧ (((p3 ∨ True) ∨ (((p2 ∨ (p5 → ((False ∧ (((p2 ∨ (p1 ∧ p4)) ∧ p2) → p4)) ∨ p3))) ∨ True) ∧ p4)) → p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2373913210959733036699522042 : (((p5 → ((p5 ∧ p4) → p2)) → (p5 ∧ ((p1 ∨ p4) ∨ p5))) ∨ (False → (((((p5 ∧ (True ∧ True)) → p2) ∨ False) → p1) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617041204191323866588734531039 : ((((((True → (p5 ∧ (p1 ∧ p4))) → (p1 ∧ p3)) ∧ ((p3 ∧ ((p2 → p2) ∧ ((p4 → p5) → (p3 → False)))) → (p1 ∧ p2))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343056520741073982159201907130 : (p2 → ((p3 → (p2 ∨ (p2 → p5))) → (p4 → ((((p3 → p4) ∧ (True → (p4 ∨ p3))) ∨ (False → p3)) → ((p1 → (p3 ∧ p2)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588263515282142326151947905840 : ((((((p1 → (p2 ∨ (p2 ∧ (p4 ∧ True)))) ∧ ((False ∧ p2) ∨ (((p5 ∧ p4) → (p3 ∨ p4)) ∨ ((p3 ∧ p3) → p4)))) ∨ p1) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341767795989002882100955071078 : (p2 → ((p1 → ((True ∨ ((((p1 → p1) ∧ (p4 → p5)) ∧ (True → p2)) → p4)) → (p5 → ((False ∨ (False ∧ p1)) ∨ p4)))) ∨ (False ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112170936305458026212690940897 : (((p3 ∧ (p1 ∨ ((p2 → ((p3 ∨ False) ∨ ((((p1 → p1) ∨ (True → p5)) ∨ (p1 → True)) ∧ (True → False)))) ∧ p4))) ∨ True) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185523465837682641919318458708 : ((p3 ∨ (((p2 ∨ (p4 ∨ p1)) ∧ (p2 ∧ (p4 ∨ p3))) → p4)) ∨ ((p1 ∨ p4) ∨ ((p4 → (False ∨ False)) → ((p4 ∨ False) → (p1 ∧ p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671338575920632767770326583376 : ((((True → ((p2 ∧ p1) ∨ (p4 ∧ ((((p2 ∨ False) → (p2 → ((p4 ∨ (p4 ∨ p4)) ∧ False))) → p3) ∧ False)))) ∨ ((True → p5) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653471385360110003084076052094 : ((((p4 → (False ∨ (((p4 ∨ (False ∧ p2)) → (((((p3 → p1) ∨ p3) ∨ ((p1 → p3) → p2)) ∨ p5) ∧ True)) ∧ False))) ∧ (True ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57405774642403016613426906242 : (((p1 ∨ (False ∧ p1)) ∨ (p2 ∧ ((p2 → (p3 ∨ False)) → (p1 ∨ ((p1 ∧ ((p1 ∨ True) ∨ (((p5 ∨ p2) ∨ p2) ∧ p5))) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50396744044116579294909178932 : ((((False ∨ True) → (((False ∧ p1) ∨ (p1 ∧ (p2 ∨ (((p4 ∧ (p1 → p2)) → p2) ∨ p4)))) ∨ p5)) ∨ ((False ∨ True) ∨ (p5 ∧ False))) ∨ False) := by
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
theorem thm_5_vars_46705701834180822625573628142 : (((p4 ∨ ((p5 → ((((False ∧ True) ∧ (False → p3)) ∨ True) ∧ (False ∨ p4))) ∨ ((p1 ∧ (p4 ∨ p1)) ∨ (p4 ∨ True)))) ∧ (p5 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184736437475920322720819093322 : ((((p5 ∨ (p3 ∨ True)) ∧ False) ∧ ((p3 ∨ p2) ∨ (True ∨ p2))) ∨ (True ∨ ((False → p4) ∨ (((p4 ∧ (p5 → False)) → (p4 ∧ False)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62772199128151358053289312210 : ((p4 ∧ (((True ∧ (((p5 ∨ (False ∨ True)) → True) → True)) ∧ ((p2 → p2) ∨ ((p3 → (True ∨ p4)) → p5))) → ((p5 → p1) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45487686488487602601641086772 : (((False ∨ ((p4 → p4) ∧ ((p5 → (p2 ∧ True)) → ((p4 ∧ (((False ∨ p4) → (p1 ∧ (p5 ∨ (p2 → False)))) ∨ p1)) ∨ True)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134377184785962825244953686985 : (((p3 ∨ ((p2 → (p3 ∨ True)) ∧ ((((p3 ∨ p3) ∨ ((p1 → p5) ∧ p2)) → p4) ∨ (p3 → (p5 ∧ p5))))) ∨ p3) ∨ (p1 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191906903235867479769846543832 : ((p5 ∨ ((True → False) ∧ (False ∧ ((False → p5) → p5)))) ∨ (((False ∨ p2) → (False → (p2 → (p2 → (p1 ∨ ((p1 → False) ∧ p2)))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117962410972804571843568734278 : ((p5 ∧ (p1 → (((p2 → ((p4 ∨ ((p1 ∨ p2) ∨ True)) ∧ p4)) ∧ ((p2 ∨ p3) ∧ ((True ∧ (p2 ∨ p1)) → p2))) → p4))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53666102776496907904151410467 : ((((p3 ∨ p1) ∨ ((p4 → (p4 ∨ (False ∨ False))) ∨ p4)) ∧ (p5 → ((p4 ∨ True) ∧ ((p4 ∨ p4) ∨ ((p1 → (p1 ∧ p1)) ∨ p2))))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8247775807003297219642170841 : ((((((((((p2 ∨ p4) ∧ p4) ∨ p4) → ((p2 ∧ p2) ∨ p4)) ∨ (True → p4)) ∧ (False ∨ ((p4 ∨ False) → True))) ∨ p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233494079030258861074235628982 : ((p1 ∨ (p2 ∧ p4)) → ((((p1 → (p4 ∨ (p4 ∧ (True → False)))) → p2) ∧ (p4 ∨ True)) ∨ (p2 ∨ (((p5 → (p2 ∧ p4)) ∧ p3) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66644692472598161596705553663 : ((True → (((((((p4 ∨ False) ∧ p1) ∧ False) ∨ p5) ∧ False) → p1) ∧ (p5 ∨ ((False ∧ p3) ∨ (((p2 → p3) → (p1 ∧ p1)) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115702813343140018323195614101 : (((((p4 → (True ∨ p2)) ∨ p2) ∧ p2) → (((((False ∧ p5) ∧ p3) ∨ True) ∨ ((((p5 ∨ p5) → False) → p2) ∨ True)) ∨ p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358520982835200873661119002647 : (p5 → (p2 → (((((p2 ∧ p3) → ((p4 ∨ (p3 → False)) ∧ (False ∨ p4))) ∧ p3) ∨ ((False ∨ ((p5 ∨ (p3 ∧ False)) ∨ p5)) → p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



