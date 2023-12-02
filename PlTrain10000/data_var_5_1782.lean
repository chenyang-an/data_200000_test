variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797377964614734833589605221827 : (((p1 → (((True ∨ (p5 ∨ p3)) ∧ ((((True ∧ False) ∨ True) → ((False ∨ ((p1 → False) ∧ (p2 ∧ False))) ∨ p3)) ∧ (p2 → p3))) ∨ p1)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_39994162182183007868699236999 : (((p5 → ((p5 ∧ ((((((p4 → True) → p2) ∧ ((p3 ∨ p1) ∧ False)) ∨ ((False ∧ p5) → True)) ∧ p1) ∧ True)) ∧ (p1 ∧ False))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41652972541486763936938345593 : (((((p1 → p4) ∧ (p2 ∧ (True ∨ False))) ∧ (((p1 → (((True ∨ (False → (False ∧ p3))) ∧ (p2 → p5)) → p4)) ∨ False) ∧ p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53874306601482036538492076866 : ((((p5 ∧ False) ∨ (((p3 → (False ∨ p2)) ∨ p4) ∨ True)) ∨ ((((((p4 ∨ ((p2 ∨ p4) ∨ p1)) → False) ∧ p1) ∧ False) ∨ p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49632392815062176664512292031 : (((((True ∨ (p1 ∨ (p4 ∨ True))) ∨ p2) → ((p5 ∧ ((p1 ∨ (p2 → p1)) → (p2 ∨ (p2 ∧ True)))) → p2)) → ((p5 ∨ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230659102438529580704897998333 : (((p3 → p2) ∧ p3) → (((p1 → p5) ∧ ((p1 ∧ p1) → ((False → p3) → (p5 ∨ ((p4 ∨ (p4 ∧ (False ∧ p5))) ∧ p4))))) ∨ (p3 ∨ False))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187474283544851839795035227864 : ((False ∨ (((p1 ∧ (True ∧ ((True → p1) → False))) → p3) ∧ p2)) → (True ∧ ((p4 ∨ (((False ∨ p1) → False) ∨ ((p2 ∨ False) ∨ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33896825857483393045077435417 : ((p5 ∨ (((p2 ∧ (p5 → p1)) ∨ p3) → ((p3 → ((p1 ∧ p2) ∨ (p4 ∨ ((p5 ∧ p3) ∨ True)))) ∨ (((p2 ∧ p5) ∧ p5) ∨ p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
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
theorem thm_5_vars_635744138480587361732238554648 : ((((((False → (p2 ∧ ((p2 ∨ ((p5 → False) ∨ False)) ∧ (((p2 → p4) ∧ p4) → p2)))) ∨ False) → (p2 ∧ ((p4 ∨ p4) ∧ p2))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228765118423794312681757209540 : ((p3 ∨ (p1 ∧ p4)) ∨ ((((p3 ∧ p3) → True) → p1) ∨ (((p3 ∧ p2) ∨ (True ∨ (False ∨ (((False ∨ p2) ∨ True) ∨ p3)))) ∨ (False ∧ p3)))) := by
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
theorem thm_5_vars_134840142068647576676568223456 : (((p3 ∨ ((False ∧ (True ∨ p2)) ∨ (((p3 ∨ True) ∧ True) ∨ (True → (p3 → ((p2 ∨ (p3 ∧ p3)) → p5)))))) → p5) ∨ ((p3 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670798515660087083457813564751 : ((((p1 ∧ ((False → (((p2 ∨ p3) ∧ p3) → (False ∧ (((p1 → p3) ∨ (p5 → p5)) ∧ (True ∨ p5))))) → p1)) ∨ (p2 ∨ (True ∨ p3))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_139930755470112330958346024023 : ((((p1 ∧ ((p4 → True) → p5)) ∧ ((True ∧ ((p2 ∧ p2) → ((p5 ∨ p3) ∨ p4))) ∨ (p3 ∧ p1))) ∧ (True ∨ p2)) → (p5 ∧ (p4 ∨ p5))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h12
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h16 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h18 := h7 h16
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h23 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h25 := h7 h23
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h27 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h29 := h7 h27
      -- One of the premise coincides with the conclusion.
      exact h29
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h30.left
  let h33 := h30.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h32.left
  let h35 := h32.right
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h39 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h40 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h41
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h42 := h35 h40
      -- One of the premise coincides with the conclusion.
      exact h42
    case inr h43 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h44 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h45
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h46 := h35 h44
      -- One of the premise coincides with the conclusion.
      exact h46
  case inr h47 =>
    -- Conjunctions on the left can always be decomposed.
    let h48 := h47.left
    let h49 := h47.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h50 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h51 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h52
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h53 := h35 h51
      -- One of the premise coincides with the conclusion.
      exact h53
    case inr h54 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h55 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h56
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h57 := h35 h55
      -- One of the premise coincides with the conclusion.
      exact h57



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264364548353439690117573554097 : (True ∧ ((p3 ∨ ((p3 ∧ True) ∨ True)) ∧ ((False ∧ p3) ∨ (((p1 ∨ False) ∨ True) ∨ (p3 ∧ (False ∧ ((((p3 ∧ p5) ∨ p4) ∧ False) ∨ False))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232162969084756895379742579941 : (((True → p4) → True) → (((p4 ∨ ((False ∧ (False ∧ (p4 ∨ (False ∧ (p2 ∨ (True ∨ p5)))))) ∨ p1)) ∨ p2) → ((p4 ∧ (p5 ∨ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619968160675278944570664640542 : (((((p1 → p3) ∧ (p2 ∧ (p3 ∨ ((((p3 ∨ True) ∧ p4) ∧ ((p5 → (False → (p5 → (p2 → p4)))) ∧ (p3 → p2))) ∨ p1)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_40155194746122003495487388389 : ((((((p5 ∧ (p2 → True)) ∧ ((p2 ∧ ((p5 ∧ True) → p3)) ∨ False)) → (p4 ∧ (p4 ∨ ((p5 ∨ (p4 → p4)) ∨ False)))) ∧ p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60565894790973273047508651027 : ((True ∧ (((p2 → ((p5 → p3) ∧ ((((p4 ∨ ((p2 ∨ (p5 ∧ p2)) ∧ p2)) → False) ∧ (False ∧ (p4 → p2))) → p4))) ∨ p5) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639915512820685142630080241456 : (((((True ∧ (p3 ∨ p1)) ∨ (((False ∧ True) ∧ (((False → ((p5 ∨ p1) ∧ p3)) → p5) ∨ (p5 → (False → (p5 → False))))) → p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59374284104545159559713158941 : (((p5 ∨ p5) ∨ ((((p1 ∧ (p4 ∨ (p2 ∧ ((True ∧ p2) ∨ p4)))) ∧ (p1 → (True ∧ p2))) → (p5 → p3)) ∧ ((p1 ∧ True) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625768836446267548338371410217 : ((((p1 → (True ∧ ((p2 → False) → (p4 ∨ ((p5 ∧ ((True ∧ (((p1 ∨ p1) → p5) ∨ p2)) ∧ (p4 ∨ False))) ∨ (False → p1)))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612451613725146756123313157638 : ((((((((((((((p3 ∨ p1) ∧ ((p1 → p5) ∧ p4)) ∨ p3) ∧ p3) ∨ p2) ∨ p2) ∧ p2) ∨ p2) → p4) ∧ False) ∨ (False ∨ p3)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665081624696240129994932716393 : ((((p5 → (((False ∧ (((p2 ∧ (p3 ∨ p5)) → ((p3 ∧ p4) ∧ ((True → p5) → p1))) ∨ p2)) → p4) ∨ (p5 → p5))) → (p2 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44849977598418155520967721846 : ((((True ∧ (p4 ∧ True)) ∨ (((False ∧ ((((p2 → (p4 → p1)) → p3) ∧ (p1 → ((p1 ∨ p3) ∧ p3))) → False)) → p2) ∧ p1)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119568703788686654019797464510 : ((p5 → ((((True ∧ p1) ∨ p3) ∧ (p4 ∨ p4)) ∧ (p2 ∨ (p2 ∨ (False ∧ ((p3 → (p5 → ((p2 ∨ p3) → p1))) ∨ p3)))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204935142243520642064035578324 : ((((p3 ∧ p5) → (p2 ∧ p1)) → p5) ∨ (((False ∧ ((p4 → (p1 → (((p3 ∧ (True → False)) ∧ p3) ∨ False))) ∨ p3)) → p4) ∨ (p2 → p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191918704218137129071298679181 : ((p5 ∨ (p2 → ((p4 ∨ ((p4 ∨ p2) ∨ p4)) ∧ False))) ∨ (((p5 ∧ p2) ∨ ((p2 ∨ p2) ∨ (p1 → False))) ∨ ((True ∨ (p5 → True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82340127237271360714429514645 : (((((p5 ∧ (True → ((((p3 ∧ True) ∧ p2) ∨ False) ∨ p1))) ∨ p1) ∧ ((p3 → (p2 ∧ False)) ∧ p4)) ∧ ((p3 ∨ (p2 → p3)) ∨ p1)) → p1) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h13 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h14 := h9 h13
        -- We need to get the right conjuct of h14 based on <expert-advice>.
        let h15 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h18 := h8 h17
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Conjunctions on the left can always be decomposed.
            let h23 := h21.left
            let h24 := h21.right
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h25 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h23
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h26 := h9 h25
            -- We need to get the right conjuct of h26 based on <expert-advice>.
            let h27 := h26.right
            -- False on the left can always be used.
            apply False.elim h27
          case inr h28 =>
            -- False on the left can always be used.
            apply False.elim h28
        case inr h29 =>
          -- One of the premise coincides with the conclusion.
          exact h29
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h5.left
    let h33 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h36 =>
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h37 =>
      -- One of the premise coincides with the conclusion.
      exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774991016241729096440950172609 : (((False ∨ ((False ∨ (p4 → p3)) ∨ ((p5 ∧ (((p4 → True) ∧ (((p1 ∧ p4) ∨ p5) ∨ (p1 ∧ (p3 ∧ p4)))) → False)) ∨ (p4 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300397888556583573838939032360 : (False ∨ (((p5 ∧ True) → (((((p4 ∨ False) ∧ True) ∨ (p4 ∨ True)) ∨ p4) → ((p1 ∨ (p3 → p5)) ∧ (p5 ∨ True)))) ∨ (p1 → (False → p1)))) := by
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
theorem thm_5_vars_191646315057344156307343906511 : ((p4 ∧ ((p4 → (p1 ∧ p3)) → ((p2 ∨ p4) ∨ p4))) ∨ ((((p2 ∨ p1) ∧ (p5 ∧ ((False ∧ (p4 ∨ (p3 ∧ False))) → p2))) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593427265691197559304987756872 : (((((((True ∧ p3) ∨ ((p4 ∧ ((p1 → (p2 ∧ False)) ∨ p1)) ∨ (p4 → p2))) → (True → (p2 → p2))) → (p4 ∨ (p4 ∧ p1))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179439036051693133130843198936 : ((p5 ∨ (((((True ∨ ((p3 ∨ p5) ∨ False)) → p2) → True) → False) ∧ p4)) ∨ ((((True ∨ p3) ∧ True) → (p4 ∨ ((True ∨ p3) ∨ False))) ∨ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343241892421180645242845410674 : (p2 → ((p3 ∨ (p1 ∨ p4)) → (p5 ∨ (p2 → (((p4 ∧ (True ∧ (((p4 → False) ∨ ((p2 ∧ p4) ∧ (False → p5))) ∨ p4))) ∨ True) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262159787200427273476334326416 : (True ∧ (((((p1 ∨ p3) → True) ∧ ((p2 → p5) → ((p1 → p1) ∧ ((p2 → p3) ∧ (p4 → (((p1 ∧ p1) → p2) → p2)))))) ∨ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321123139051972495631674496812 : (p4 ∨ (p2 ∨ ((p1 → (((True ∧ p4) → (p2 ∧ (p4 ∨ (False ∨ p1)))) ∧ ((p3 → (False ∧ p1)) → ((p3 ∨ p3) ∧ True)))) ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207750358034047136113734056157 : (((False ∨ ((False ∨ p3) ∨ True)) → False) → (((p5 ∨ (p3 ∧ (p5 ∨ (p2 ∨ ((p1 → (p4 ∨ (False ∨ (p3 ∨ p3)))) ∨ p2))))) ∨ False) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((False ∨ p3) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ ((False ∨ p3) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161840236997743055875027610403 : ((True → ((((p5 ∧ (p3 ∧ p4)) ∧ (p5 ∨ (p4 → True))) → p4) ∧ (False ∨ (p2 ∧ (True → p4))))) → ((((p4 ∨ True) ∨ p2) ∨ True) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59166857978359127080862030034 : (((False ∨ p3) ∨ ((((True → p2) ∨ p1) ∧ (((True → p5) ∨ True) ∧ (p3 ∨ p4))) ∨ ((True → True) ∨ (p2 ∨ ((p2 ∨ True) ∧ p4))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227145316882474740402549483159 : (((p5 ∨ False) → p4) ∨ ((((False ∨ False) ∧ p2) ∨ ((p4 ∨ (True → ((p2 ∧ p5) → p4))) ∨ (((p5 ∨ p5) ∨ True) ∨ (False → p1)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135969979078114615247519657165 : (((p5 → ((p3 → (p5 ∧ ((p4 → False) ∨ True))) → p5)) ∧ ((((False → p1) → (p3 → p3)) → p2) → (p1 ∧ p1))) ∨ ((p1 → p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66244155990566072729497728938 : ((p5 ∨ ((p4 ∨ (((True ∨ p1) → p1) ∧ p2)) ∨ (p5 ∨ (p5 ∧ (False ∨ (((((p1 ∨ False) ∧ True) ∧ p4) ∧ (False ∨ p1)) ∨ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757634961677200893316964476921 : (((p1 ∧ (p4 ∧ ((p2 → (((((p5 → p2) ∧ p5) ∨ (((True ∧ p2) ∧ (p4 ∨ p3)) → p1)) → (p1 ∨ p5)) → p3)) → (True → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358494982253336718830454815295 : (p5 → (p1 → ((p1 ∨ p3) → (((p2 ∧ True) ∧ p5) ∨ ((p4 → (p4 ∨ p1)) → (((False ∨ ((p1 → (p5 ∨ p5)) ∧ p2)) → False) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55990509788267113853005096962 : ((((p2 ∨ (p3 → p1)) ∧ p2) ∨ ((p4 → ((p2 ∨ p4) ∧ (p2 → (((p3 ∧ False) ∧ (p3 ∧ p2)) ∧ False)))) ∧ ((p5 → p2) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607999119642164601044515805333 : (((((p4 → ((True ∧ (True → (((False ∨ (p2 ∧ ((False ∨ (p4 ∨ p3)) ∧ (True ∨ True)))) ∧ p3) → (p2 → p2)))) → p5)) ∧ p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55922427672908184334334619548 : (((False → ((p5 ∧ p1) → True)) ∧ (((p5 ∨ (p5 ∧ p4)) → ((p3 ∨ p1) → (((True ∧ False) → (p3 ∨ p2)) ∧ (p2 ∨ p3)))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_52922389095867348273312532135 : ((((((p4 → (p5 → (p2 → (p4 ∨ p3)))) → p1) ∨ p5) ∧ False) ∧ ((((p4 ∨ p2) ∨ p3) ∨ p1) ∧ (p4 ∨ ((False ∧ True) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51665196553638818242119265707 : (((((p3 ∧ (p4 → p1)) ∨ ((p2 → p4) ∧ (((p4 ∨ p3) ∨ False) ∧ p5))) → p4) ∧ ((((p1 ∧ False) ∨ (True ∧ p2)) ∧ False) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354801298133754737671448591003 : (p5 → ((((False → (True ∧ p4)) → p2) ∧ (p1 ∨ (p3 → ((p2 ∧ ((p1 ∨ p3) ∨ p4)) ∧ ((False → p4) ∧ (False ∨ (False → False))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112391607556120256088028561395 : ((((((p2 ∧ p3) → ((p5 ∧ p2) ∨ p3)) → ((p2 ∧ (True → (False ∧ p3))) → (True ∧ (False ∧ (False → True))))) ∧ p3) → False) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642160170999859143706990016675 : ((((True ∧ ((p1 ∧ (p5 ∧ p2)) ∨ (((p3 → p5) ∧ p2) ∨ (p4 ∨ (True ∨ ((p3 → (p4 ∨ p5)) → (p5 ∧ (True ∧ p4)))))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160146716711067782090688066111 : (((((True ∧ (p3 ∨ (((p5 ∨ p2) ∨ p5) ∨ True))) → (p2 ∧ p3)) ∧ (p4 ∨ p4)) ∧ (p1 ∧ p1)) → ((True ∧ ((p3 → False) ∨ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655344813277818829337038836690 : (((((((False ∨ p4) → (p3 ∨ (((p4 → ((p3 ∨ p5) → (False ∧ (p2 ∧ p1)))) ∧ p1) → p2))) ∧ False) ∨ (False ∨ p3)) ∨ (False → p3)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_123112689592594697792187995275 : (((((p2 ∧ p2) ∨ (True → (p1 ∧ (True → ((False ∨ p4) ∨ (p4 ∨ True)))))) → ((False ∧ p4) ∧ p4)) → ((p5 ∧ p4) ∧ p2)) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52405272955646637090695906191 : (((((p4 → p2) ∧ False) ∧ ((True ∧ (False → False)) ∧ ((False ∧ True) ∨ False))) ∧ ((((p4 ∨ False) ∨ ((p2 ∨ False) ∧ p1)) ∨ p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751211451147773766630184198711 : (((True ∧ (((p4 → p1) ∨ True) → (((((p3 ∨ (False ∧ (p2 → (True ∧ False)))) ∨ p5) → ((p5 ∧ False) ∨ p1)) ∨ True) ∧ (False → p1)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702574428074718380656838505527 : ((((((p2 ∧ p3) ∨ ((p2 ∨ (p4 ∧ p5)) → p1)) → False) ∨ ((False → (p1 ∨ ((True ∨ False) → (p2 → p4)))) ∨ ((p4 ∧ p3) ∧ False))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144788093512563711345012722187 : (((p5 ∧ (p3 ∨ (((False → True) ∨ p5) ∧ ((((p4 ∧ p5) ∨ p3) ∧ p5) ∧ True)))) ∨ ((True ∨ p3) ∨ p2)) ∧ (((p4 ∨ True) ∧ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64045396301900354987455521698 : ((False ∨ (((((True → p4) ∨ p2) ∧ (True ∨ ((True → False) ∨ (((p3 ∧ p1) ∧ (p5 ∨ p4)) → False)))) ∨ True) → ((p4 ∧ p2) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164836006901420958931016831932 : (((p1 ∧ ((p5 → ((p3 → (p1 → False)) ∨ p1)) ∧ ((p3 ∨ (p5 ∨ p1)) ∧ p5))) ∨ p3) ∨ (p1 → (((p1 → True) ∧ True) ∨ (p4 ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198213495994829449315717718483 : (((p5 → p4) → (((p2 → p4) ∨ False) ∧ p5)) ∨ ((((p1 → p2) ∨ p4) ∧ ((((p1 → p4) ∧ True) ∨ False) → (False ∧ (True → p1)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136745712392205779383886761379 : (((p1 ∨ False) ∧ ((p3 → ((p5 → ((p1 → p4) ∨ p1)) ∨ (p1 ∨ ((p5 ∧ p2) ∧ p1)))) ∧ (False ∧ (p5 ∨ False)))) ∨ (True ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_584714041357797047479645471 : (((((p4 → (False ∧ (p5 ∨ (p2 ∧ True)))) ∨ (p2 → True)) ∧ (p1 → (p3 ∨ ((True ∧ p1) ∧ (False ∨ (p2 → p5)))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51908532820683572342674729513 : ((((((((p2 ∨ p1) ∧ (p2 ∧ True)) ∨ (True ∧ p2)) ∨ p2) ∧ False) ∨ (p5 ∧ p1)) ∨ (((p5 ∨ p5) → (True → (p5 → True))) ∨ p4)) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49764131776154296950752485077 : (((False ∨ (((False → p3) → (p1 ∨ p2)) ∧ ((p1 ∧ p3) → ((p4 ∧ (p2 ∨ True)) ∨ ((p5 ∨ p5) ∨ False))))) → (p2 ∨ (p1 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185990933212689173924519724189 : (((p2 ∨ ((p1 ∨ (p4 → (True → (p1 ∨ p5)))) ∧ p1)) ∧ p4) → (((((p5 ∧ (((p1 → p5) → False) ∧ True)) → False) ∧ p2) ∨ p1) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115559672747652065470482268386 : ((((((True ∨ p2) → False) ∨ p4) ∨ p5) ∧ ((p4 ∨ ((p5 ∧ ((p1 → (p3 → p3)) → (p5 ∨ p5))) ∨ p2)) ∧ (True ∨ p5))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336099882981224937320951320668 : (p1 → (((p3 ∨ ((((p2 → (True → p2)) ∧ p2) ∨ p3) ∧ (((((p4 ∧ p5) → (True ∧ p3)) ∨ p2) ∨ (p3 ∨ p5)) → p3))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349397959739177879437327517199 : (p3 → (p4 → ((p1 ∧ (p2 → (((((p4 → (True ∧ (False ∧ p4))) → p3) ∨ (p1 ∨ (False ∨ ((False ∧ False) ∨ p3)))) → True) → False))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68576495040839292913945761754 : ((p4 → (((p5 ∧ (((((False → p3) ∨ p3) ∧ p1) ∨ p3) → p5)) ∧ ((p4 ∧ (True → p4)) ∨ ((p1 ∧ False) ∨ (p1 ∧ p2)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675660856403792205855279679539 : (((((((p3 → ((p1 ∨ (p3 ∨ (p3 ∨ p5))) → False)) ∧ p1) ∨ (p5 ∨ (p1 ∨ False))) → (False ∨ True)) ∧ ((p4 ∧ (p2 ∧ p4)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159010293318331303557849197188 : ((p4 ∨ ((((((p1 ∧ (p2 ∨ False)) ∧ p4) ∨ ((p4 → p1) → p3)) ∧ (p4 → p1)) → p3) → p2)) ∨ (False → (((p1 ∨ False) → p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51145373007677887465669186877 : (((((p2 ∧ ((p3 ∨ (p2 → ((p1 → p4) ∧ p2))) ∧ p3)) ∨ (p5 ∨ (p4 ∧ p3))) → p2) ∨ (p5 → (((p2 ∨ True) → False) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60244547556083413914857868285 : (((False → True) → (((p1 ∧ ((True → (p1 ∨ False)) → (p3 ∨ (False → (p2 → ((p3 ∨ p4) ∨ p5)))))) ∨ (p5 ∧ (p5 ∧ p2))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47284529673580373253009948745 : ((((((p5 → p1) ∧ p5) ∨ False) → ((False ∧ ((p1 ∨ p5) → ((p3 ∧ ((p5 → (True ∨ p2)) → p1)) ∨ p3))) ∧ p1)) ∨ (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337882842942319092607047003334 : (p1 → ((((True ∨ p3) ∧ (((p3 ∨ (p4 ∨ (False → p1))) ∨ p4) ∧ p1)) ∨ p1) → (((p2 ∧ (p1 ∧ p5)) → p4) → ((p3 ∨ p3) ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h6.left
      let h18 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133788762685518439346816598380 : ((((p4 ∨ (False ∨ p2)) ∧ (((p5 → (((False ∨ False) ∧ ((p5 ∨ (False ∨ p3)) ∨ p3)) → p2)) → p1) → p4)) ∧ p1) ∨ ((False ∧ False) → p1)) := by
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
theorem thm_5_vars_354826303257028661680333849231 : (p5 → ((((p3 → True) ∧ p2) → ((((((p2 ∨ (True → p5)) → (((p5 ∧ p2) → p1) ∧ p5)) ∨ p1) ∧ False) ∧ (p4 ∨ p2)) ∨ p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52120138170405165462363070694 : (((((p5 ∨ (True ∧ p5)) → ((p1 ∧ False) → ((p1 ∧ (False → p2)) ∨ p5))) → p1) → ((p1 ∧ (p1 ∧ (p5 ∧ p5))) ∨ (p1 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318168496684255389156781327987 : (p4 ∨ (((((p2 ∨ (p4 → True)) ∧ (((True ∧ False) ∨ (p5 ∨ (p3 ∧ (True → p1)))) ∨ p1)) ∧ p4) ∧ ((p5 ∨ (True → p1)) → False)) → False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h15 : (p5 ∨ (True → p1)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h16 := h3 h15
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h20 : (p5 ∨ (True → p1)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
            have h22 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h19, we can now drive its conclusion.
            let h23 := h19 h22
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h24 := h3 h20
          -- False on the left can always be used.
          apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h26 : (p5 ∨ (True → p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h28 := h3 h26
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h36 : (p5 ∨ (True → p1)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h35
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h37 := h3 h36
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h41 : (p5 ∨ (True → p1)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h42
            -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
            have h43 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h40, we can now drive its conclusion.
            let h44 := h40 h43
            -- One of the premise coincides with the conclusion.
            exact h44
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h45 := h3 h41
          -- False on the left can always be used.
          apply False.elim h45
    case inr h46 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h47 : (p5 ∨ (True → p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h48
        -- One of the premise coincides with the conclusion.
        exact h46
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h49 := h3 h47
      -- False on the left can always be used.
      apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46931167770587412001188879023 : (((((p1 ∨ p4) → ((p5 → (((p3 ∨ ((p3 ∧ p4) ∨ p1)) ∨ p5) ∨ (p1 ∨ (p2 ∨ p2)))) ∧ (p3 ∧ p3))) ∨ p5) ∨ (p4 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315188884178683967850045338212 : (p3 ∨ ((((p2 ∨ p1) → True) ∨ True) ∧ ((((p4 ∧ ((p1 → (p3 → p5)) → (p5 → (p5 ∨ p5)))) ∨ False) ∨ ((p1 ∧ p3) → p1)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_134823759702997714953806919763 : (((False ∨ (p4 → ((((True ∧ p5) ∧ (p1 → ((p2 ∨ p5) ∧ (True → p3)))) → p2) ∧ (p1 ∨ (p1 ∧ p5))))) → False) ∨ (True ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801513550742268520117087421211 : (((p2 → (((False ∨ ((p5 ∨ (p5 ∧ p3)) ∧ False)) → p1) → (((((False → p2) ∧ p4) ∨ p3) ∨ ((p2 ∨ p3) → p4)) ∨ (True → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347402433045186363748416360429 : (p3 → ((((p3 ∧ p4) ∨ (p4 → (p2 ∨ p2))) ∨ p5) → ((p4 ∧ p2) ∨ ((p3 ∨ (p5 ∨ p1)) ∨ (((p1 → p2) → p5) → (p2 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111384380614722989170047747338 : (((False ∨ ((p3 → ((((True ∧ False) ∨ p3) ∧ (False ∨ (False ∨ p2))) ∨ False)) → ((((False ∧ True) ∧ False) ∨ False) ∧ p4))) ∧ True) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301153334950484977530931833778 : (False ∨ (((p5 ∧ p1) ∨ (False ∧ (p2 → (p1 ∧ True)))) ∨ (((p5 ∨ p2) ∨ (p1 ∧ p4)) ∨ ((p4 ∨ False) → ((p4 → (p1 ∧ p4)) → p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119367068554705569276928296370 : ((p3 → (False ∨ (((((p1 ∨ (p4 ∨ ((False → (p1 ∧ p4)) → p3))) ∨ p1) ∧ (False ∨ False)) ∧ p1) ∨ ((p4 ∧ p1) ∨ p3)))) ∨ (p3 ∨ False)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118126199905486264786479539959 : ((False ∨ (((p5 ∨ p2) ∧ ((((p5 ∧ p5) ∧ True) ∧ (p5 → (p3 ∨ p4))) → (p2 ∨ ((p1 → p5) → p1)))) ∨ (True → True))) ∨ (True ∧ p2)) := by
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
theorem thm_5_vars_319570666221063118669762084599 : (p4 ∨ ((((p3 → (False → ((p3 ∧ True) ∧ p4))) ∨ p3) → p3) → ((p1 ∨ ((p3 ∨ p2) ∧ (((p2 → p1) ∧ (p2 ∨ p3)) → True))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → (False → ((p3 ∧ True) ∧ p4))) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224330849054163749520049274119 : ((False → (p4 ∨ False)) ∧ (((p3 ∧ ((p5 ∨ p1) ∧ (p3 ∨ p5))) ∨ p5) → (p2 ∨ (p3 → (((p4 → (False → (p3 → p5))) ∧ p5) → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Implications on the right can always be decomposed.
        intro h27
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- One of the premise coincides with the conclusion.
        exact h29
  case inr h30 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h31
    -- Implications on the right can always be decomposed.
    intro h32
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- One of the premise coincides with the conclusion.
    exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115531129414908398978916524906 : (((p3 ∧ (((True ∨ False) ∧ (True ∨ p1)) ∨ p5)) → (((p4 ∨ p1) → ((p1 ∨ (p5 → (p3 ∨ p4))) ∧ p4)) ∨ (p4 ∧ p3))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48907338611945251600671237939 : (((p4 → ((False → (p5 ∨ p2)) → (p3 → (((False → ((p2 ∨ p2) → p4)) ∧ p2) ∧ (p3 ∧ (p2 ∨ True)))))) ∧ ((True ∧ p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150271143481628169010781323888 : ((p3 → (False ∨ ((((p2 ∨ (p5 ∧ False)) → p3) → (p3 → (p1 ∨ False))) ∧ (((True ∧ p2) ∧ True) ∨ p5)))) ∨ (((True → False) ∧ p2) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780520711533017628541471799346 : (((p2 ∨ ((False ∧ ((((p5 ∧ p3) ∨ (p2 ∨ p3)) ∧ (p2 ∧ p5)) ∨ True)) ∧ ((p4 ∧ ((p1 ∧ True) → p2)) → ((p1 ∨ p4) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42747548147606655726410725933 : (((True → ((False ∨ p3) ∧ ((p1 ∨ (p4 ∧ ((((p4 ∨ (((True ∧ False) ∧ p4) → (p4 → p2))) → p4) → True) ∨ p4))) ∧ p5))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932369366447026370837150670025 : ((((((p3 ∧ p3) ∨ True) ∧ (p1 → (p4 ∨ p4))) ∧ (((p4 ∨ (p2 ∧ True)) ∨ (p3 ∨ p4)) ∧ (((False ∧ p5) → p4) → (p5 ∧ False)))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h13 : ((False ∧ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h15
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h17 := h10 h13
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h22 : ((False ∧ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- False on the left can always be used.
          apply False.elim h24
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h26 := h10 h22
        -- We need to get the right conjuct of h26 based on <expert-advice>.
        let h27 := h26.right
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h30 : ((False ∧ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h31
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- False on the left can always be used.
          apply False.elim h32
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h34 := h10 h30
        -- We need to get the right conjuct of h34 based on <expert-advice>.
        let h35 := h34.right
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h37 : ((False ∧ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h38
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- False on the left can always be used.
          apply False.elim h39
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h41 := h10 h37
        -- We need to get the right conjuct of h41 based on <expert-advice>.
        let h42 := h41.right
        -- False on the left can always be used.
        apply False.elim h42
  case inr h43 =>
    -- Conjunctions on the left can always be decomposed.
    let h44 := h3.left
    let h45 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h46 =>
      -- Disjunctions on the left can always be decomposed.
      cases h46
      case inl h47 =>
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h48 : ((False ∧ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h49
          -- Conjunctions on the left can always be decomposed.
          let h50 := h49.left
          let h51 := h49.right
          -- False on the left can always be used.
          apply False.elim h50
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h52 := h45 h48
        -- We need to get the right conjuct of h52 based on <expert-advice>.
        let h53 := h52.right
        -- False on the left can always be used.
        apply False.elim h53
      case inr h54 =>
        -- Conjunctions on the left can always be decomposed.
        let h55 := h54.left
        let h56 := h54.right
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h57 : ((False ∧ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h58
          -- Conjunctions on the left can always be decomposed.
          let h59 := h58.left
          let h60 := h58.right
          -- False on the left can always be used.
          apply False.elim h59
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h61 := h45 h57
        -- We need to get the right conjuct of h61 based on <expert-advice>.
        let h62 := h61.right
        -- False on the left can always be used.
        apply False.elim h62
    case inr h63 =>
      -- Disjunctions on the left can always be decomposed.
      cases h63
      case inl h64 =>
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h65 : ((False ∧ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h66
          -- Conjunctions on the left can always be decomposed.
          let h67 := h66.left
          let h68 := h66.right
          -- False on the left can always be used.
          apply False.elim h67
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h69 := h45 h65
        -- We need to get the right conjuct of h69 based on <expert-advice>.
        let h70 := h69.right
        -- False on the left can always be used.
        apply False.elim h70
      case inr h71 =>
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h72 : ((False ∧ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h73
          -- Conjunctions on the left can always be decomposed.
          let h74 := h73.left
          let h75 := h73.right
          -- False on the left can always be used.
          apply False.elim h74
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h76 := h45 h72
        -- We need to get the right conjuct of h76 based on <expert-advice>.
        let h77 := h76.right
        -- False on the left can always be used.
        apply False.elim h77
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234887090648245108003484083264 : ((p5 → (p5 → p2)) → (((True → p1) → (False ∧ p2)) ∨ (((p1 ∧ ((p1 ∨ p1) ∧ ((p1 ∧ p5) → ((p1 → p5) ∨ p4)))) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305163114636231936413412519119 : (p1 ∨ ((((((((True → (True ∨ p2)) ∨ (p2 → (p3 ∨ True))) → (p3 ∧ p4)) ∨ p4) ∨ p5) ∨ p3) → p2) ∨ (False → ((False ∧ p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



