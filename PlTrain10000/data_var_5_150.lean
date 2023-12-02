variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157545361096392304679252184317 : (((((p5 ∨ ((False ∧ (p3 ∨ (p4 ∨ True))) ∨ (p1 → True))) ∨ (p4 ∨ True)) → p1) → (False ∧ p4)) ∨ (((p1 ∨ p5) ∨ p3) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_172507841507029721062549449018 : ((((True ∨ p1) ∨ True) ∧ (p5 ∧ ((False ∧ (True ∨ p2)) ∨ (p5 → (p2 ∨ p3))))) ∨ (((((False ∨ p4) ∨ p1) ∧ p5) ∨ (False → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692431576359862072740459626061 : (((((((((p2 → p5) ∨ False) ∨ p4) ∧ (True ∧ p1)) ∧ p2) ∧ (p2 ∨ p5)) ∧ (p4 ∨ ((p4 ∨ ((p2 ∨ False) ∨ (p1 → p4))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671195844488412495179443799913 : ((((p3 ∨ (((False ∨ ((p3 ∧ ((p3 → p2) ∨ p3)) ∧ (True ∨ p3))) ∨ (p2 ∨ p5)) ∨ (False ∧ (False ∨ False)))) ∨ ((p1 ∧ p3) → p3)) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184844077686775761488903998536 : (((p3 ∨ ((p4 → p2) ∨ p1)) → (p5 ∨ ((p1 → False) ∧ p3))) ∨ (((((p3 ∨ p5) → p3) → (p1 → (p4 ∧ False))) ∧ p3) → (p4 → p3))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227786632854401074650943262256 : ((p1 ∧ (p2 → p4)) ∨ ((((p4 ∨ p4) ∨ (p3 ∧ (p2 ∨ p2))) ∨ (p3 ∨ False)) ∨ (p5 → (((p5 → p3) ∨ ((p4 → p4) ∧ p4)) ∨ p5)))) := by
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
theorem thm_5_vars_111632494663807506756389481013 : ((((((p5 ∧ ((p4 → (p3 ∧ (p4 ∧ p3))) ∨ True)) ∨ ((True → False) ∧ p5)) ∨ (((True → p4) ∧ p2) ∨ p3)) ∨ p3) ∨ True) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775400864815862524187240041596 : (((False ∨ (p2 ∧ ((((((p4 ∨ p5) → p4) ∧ ((False → (p4 ∨ p3)) → p3)) ∨ (p1 ∧ ((p1 ∨ (p5 ∧ p4)) ∧ True))) ∨ p5) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215083456066446938810817814725 : (((True → p5) → (p5 ∧ p2)) ∨ (p3 → (p5 → (((p1 ∨ p1) → (p5 ∨ (p4 ∨ (p2 ∨ False)))) → (((p5 → (p5 ∨ p1)) → p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115190938010034126444959030462 : ((((p4 → (False ∧ (p5 ∧ p5))) → (False ∨ (True ∧ p3))) ∧ ((True ∧ (((p5 → ((p5 ∨ False) ∨ p4)) ∨ False) ∨ p4)) → p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563356642003860293990619480710 : (((p5 ∨ (((p2 ∨ p2) ∧ p3) → ((p4 ∨ (p4 ∧ (p1 ∧ ((p5 ∨ p2) ∨ ((False ∧ p3) ∧ p4))))) → ((p5 ∨ p2) ∧ (p3 ∧ True))))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- False on the left can always be used.
      apply False.elim h27
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- One of the premise coincides with the conclusion.
      exact h31
    case inr h33 =>
      -- One of the premise coincides with the conclusion.
      exact h31
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h1.left
        let h42 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h43 =>
          -- One of the premise coincides with the conclusion.
          exact h42
        case inr h44 =>
          -- One of the premise coincides with the conclusion.
          exact h42
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h1.left
        let h47 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h48 =>
          -- One of the premise coincides with the conclusion.
          exact h47
        case inr h49 =>
          -- One of the premise coincides with the conclusion.
          exact h47
    case inr h50 =>
      -- Conjunctions on the left can always be decomposed.
      let h51 := h50.left
      let h52 := h50.right
      -- Conjunctions on the left can always be decomposed.
      let h53 := h51.left
      let h54 := h51.right
      -- False on the left can always be used.
      apply False.elim h53
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158547276562364956980358327886 : (((p4 → False) → ((False → (p2 ∧ ((False ∨ p3) → (False ∨ p1)))) ∧ ((False ∨ p3) ∧ (p3 ∨ p1)))) ∨ ((p3 → (True → (p3 ∨ p4))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40975241672787231844692206789 : (((((True ∨ True) ∧ ((p4 → (p3 ∧ p2)) → (((False ∧ (False → (p5 ∨ ((True ∨ p3) → p5)))) ∧ p4) ∨ p5))) ∨ (False → p5)) ∨ p1) ∨ p1) := by
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
theorem thm_5_vars_39884929705884296749786347809 : (((p2 → ((p4 ∧ ((True ∨ True) ∧ ((p5 ∨ p3) ∧ p2))) ∨ (True ∧ ((p1 ∧ True) ∧ ((((p5 ∨ p3) → p1) ∧ p5) ∨ False))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184362148233421334208337031345 : (((p1 ∨ (p4 ∧ ((p5 ∧ ((False ∨ p5) ∧ p2)) → p5))) → p3) ∨ ((p1 ∨ False) ∨ (True ∨ ((True ∧ p5) ∨ (p3 ∨ ((p3 ∨ p1) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50301906574816189386675876836 : ((((((((True → p4) ∧ p3) ∨ (p4 → p5)) ∨ False) ∧ ((False ∧ p4) ∨ p3)) → ((p4 ∧ p4) ∧ p1)) ∨ (((p5 ∨ p1) → p3) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134158558937094686019995151644 : (((((((False ∨ (False ∧ p2)) ∧ p3) ∨ ((False ∨ False) ∨ p1)) → ((p1 → p5) → p5)) → ((True ∨ p5) ∧ p4)) ∨ False) ∨ (False → (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260362758416438887055984449287 : ((p2 → p5) → ((p3 → ((True ∨ p3) ∧ ((p4 ∨ ((True ∧ False) ∧ (False ∨ p3))) ∨ (p3 ∧ p1)))) ∨ (p4 ∨ ((p5 → (p2 → p2)) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668811644104322619445499418660 : (((((((((p4 → ((p2 → (p2 → p5)) → p1)) ∧ p1) ∧ p5) → p4) ∨ (((p1 ∨ p2) ∨ p4) → False)) ∨ p2) ∨ (p3 → (p2 → True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175423042751612103534840658541 : ((False → (p4 ∨ ((((p4 ∧ (p5 ∨ p1)) ∨ (p3 ∧ (p3 ∨ p3))) ∧ True) → p2))) → (p3 ∨ ((p2 ∨ ((False ∧ (p2 ∧ False)) → p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160591217401363446527574475754 : ((((((p1 ∧ (p3 ∨ (p4 → p2))) → False) ∨ p2) → True) ∧ (((p1 ∧ (False ∨ p1)) ∧ p2) ∧ p3)) → ((p1 → (p5 ∨ (False ∨ p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321476497528381756206784940523 : (p4 ∨ (p1 → (((True → ((p3 ∨ p5) ∧ p2)) ∨ (((p5 ∧ (True → ((True → p1) → False))) ∧ ((p5 → False) ∨ p2)) → (p2 ∧ False))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h15 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h20 := h14 h19
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : (True → p1) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h23 := h20 h21
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265864487172439247107433493507 : (True ∧ (p5 ∨ (True → ((p5 ∧ True) ∨ (((p2 ∧ (p3 ∨ (p5 → (p1 ∨ p5)))) ∨ p5) ∨ (True ∨ ((True → ((False ∧ p3) → False)) ∨ p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337082850309913331291087789050 : (p1 → ((((((False → True) → (True ∧ (p1 ∧ (p4 ∧ ((False ∧ p4) ∨ p1))))) ∨ p2) ∧ p5) ∨ (True ∨ (True → (False → False)))) ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340970351711058041366215919730 : (p2 → (((True → p5) ∧ (p1 ∧ (((True ∧ p2) ∧ p5) ∨ (((p3 ∧ p2) ∨ (((False ∨ True) ∧ (p3 ∧ (p4 ∧ p5))) ∧ False)) ∨ p1)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48889616866396757179548578766 : (((p1 → (p4 ∧ ((p5 ∧ ((False ∧ (p3 ∧ False)) ∧ (((p5 ∧ False) ∨ True) → ((False → p1) → p1)))) ∨ False))) ∧ ((p1 → True) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345472374996738385829671478364 : (p3 → (((((False ∧ (p1 ∧ False)) ∧ True) ∧ (p4 ∧ (False ∨ ((True ∨ (p4 ∧ ((p1 → p4) ∨ p1))) ∨ p3)))) ∨ (p1 → (p1 ∧ p3))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349317947603516664730243057400 : (p3 → (p2 → (p1 ∨ (((p2 → (((p1 ∧ (False ∨ (False → (p4 ∧ p1)))) ∧ False) ∧ ((False → (p1 ∨ True)) ∨ p3))) ∨ p1) ∨ (True ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54803449002637773920289013374 : (((p1 ∨ ((p3 → ((False ∧ p1) ∨ p3)) → p3)) → (((True ∨ True) ∧ (p1 → ((p1 → ((p3 ∨ p3) ∧ p1)) ∧ (p2 ∨ p3)))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195701310495767692022321637562 : (((p5 ∧ p1) ∨ (((p4 → p3) → p4) → True)) ∧ ((((((p4 → True) → p5) ∧ p4) → (p3 ∧ p3)) ∨ ((p4 ∧ p4) ∧ True)) ∨ (p1 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647845344247881352097094413760 : (((((((p3 → ((p5 ∨ ((p2 ∧ False) → (p5 → (p4 ∧ ((p2 ∨ p2) ∧ p2))))) → p1)) → (p3 → p4)) ∨ p5) ∧ p4) ∧ (p2 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767296319939227174075831643589 : (((p5 ∧ ((((p1 → ((p2 ∧ ((False ∨ p4) ∨ (p5 ∧ (p2 → p4)))) ∨ p4)) ∧ (True ∧ p4)) → (p4 → ((p1 → False) ∧ False))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300156467757092994830704027988 : (False ∨ ((p5 ∨ (p5 → (((p5 → p4) ∨ (((p3 → (p5 → p2)) ∧ p1) → (p3 ∧ p5))) ∨ (False ∨ ((p1 → p1) ∧ p4))))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_878949771986098954222353439916 : ((((p5 ∧ (((True ∧ ((p2 → (True → p4)) ∨ (((p4 → p2) ∨ True) ∧ ((p5 ∧ (p1 ∧ False)) → False)))) ∨ p1) → p3)) ∧ (False → p2)) → p3) ∧ True) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((True ∧ ((p2 → (True → p4)) ∨ (((p4 → p2) ∨ True) ∧ ((p5 ∧ (p1 ∧ False)) → False)))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227468430599731424062713675271 : ((True ∧ (p2 ∧ False)) ∨ (((p4 ∧ (p1 ∧ ((True → p2) → (p5 ∨ p5)))) ∨ ((p4 ∨ ((True ∧ p4) ∨ p2)) ∧ p2)) ∨ (p4 → (False → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86036273098816673456708665457 : ((((False → p1) → ((((p1 ∧ p4) ∧ True) ∧ False) → p1)) ∧ (True → (True ∧ (((True → (True ∨ (p2 ∨ (p4 ∧ p4)))) ∧ p1) ∧ p4)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198307147193742810666374393266 : ((p1 ∧ (((p2 ∨ p3) → p4) → (p4 ∨ p3))) ∨ (((p1 → p5) ∨ p2) → ((((((p2 ∧ p3) → (p3 ∧ p4)) ∨ True) ∧ False) ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255982436845998286014345568397 : ((True ∨ p3) → ((((p5 ∧ p4) ∧ p5) ∨ (((p3 ∧ (((p1 → p3) ∧ (True ∧ (p5 ∧ p5))) ∨ False)) ∨ True) ∨ (p4 ∧ False))) ∨ (p3 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_451501759981565747933661661059 : (((((((False ∧ p3) ∨ ((p2 → p1) ∧ (((p5 ∧ p5) ∧ p1) ∨ p3))) ∨ p1) ∨ ((True ∨ False) ∨ p5)) ∨ (p2 ∨ ((p1 → True) → p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766800273577836630912601554187 : (((p4 ∧ (p3 ∨ (((((((True ∧ p4) → False) ∧ p2) ∨ ((p5 ∧ p5) ∧ (False → p3))) ∧ p1) ∨ True) ∧ (p3 → ((True → p1) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300688274520766691167551387053 : (False ∨ ((True ∧ (((((p4 → ((p3 → p3) → p5)) → False) ∧ p3) → p4) ∨ ((p1 ∧ p4) ∧ p3))) ∨ (((p3 ∧ p3) ∧ p1) → (p3 ∧ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301816703634414402984106075239 : (False ∨ ((False ∨ p4) ∨ ((p5 ∨ (p4 ∧ (p2 → (p2 → (p3 ∧ ((p2 ∨ ((False → True) ∨ p2)) → (True → ((p3 ∧ True) → p3)))))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146916485575459858388864519392 : ((((((((False → True) → p2) ∨ p1) ∨ False) ∧ ((False ∨ (((True → p1) ∧ p2) ∧ p1)) → p4)) ∧ True) ∧ p3) ∨ (((p2 ∨ p2) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177882891757485754035749670985 : (((((p2 → (p3 → False)) ∨ (p1 ∨ (p3 ∧ (True → p4)))) → p2) ∨ p5) ∨ ((((p1 → p5) → (p3 → ((p4 ∨ p2) ∨ p2))) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197985480917810900497819928987 : (((p3 ∨ p2) ∧ (((p5 → p5) → p1) → p3)) ∨ ((p2 → (p3 ∧ ((p2 ∧ p5) → False))) → (((False ∨ (False ∨ p1)) ∧ (p3 → p4)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218437881672380510942452246281 : (((p3 ∧ False) → (p2 → False)) → ((((p2 ∧ p2) ∨ p3) → (((p1 → False) ∧ ((p2 ∧ p1) ∧ True)) ∨ p5)) ∨ (((p3 ∧ True) ∨ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717969007913364058142448562902 : (((((p5 → (p1 → False)) ∧ p5) ∨ ((((((((p5 ∧ p1) ∧ True) ∨ p1) ∧ p3) ∨ (p3 ∧ False)) → p2) ∧ p3) ∧ (p2 → (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133995906808971734626257732799 : (((((((p3 ∨ p3) ∧ (p3 ∨ True)) → False) ∨ (p1 ∨ (((True → False) → (p2 ∨ p2)) ∧ (False → p1)))) ∧ False) ∨ p1) ∨ (True ∨ (True → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350949462382986071241306919311 : (p4 → ((((p4 ∨ (((True → p1) → ((p1 ∧ (p2 ∧ p5)) ∨ p5)) ∨ (False ∨ p1))) ∧ (p4 ∨ p1)) → (p2 ∨ (False → p5))) ∨ (False ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233562643916444156593325252402 : ((p1 ∨ (False → p5)) → (False ∨ (((((((p4 → p1) ∧ p2) → p3) ∧ (p1 ∨ (p4 ∨ False))) ∧ (True ∧ p5)) ∨ (False ∨ (p4 ∨ False))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133566078109926431773946176232 : (((((((True → ((((p5 ∨ p1) ∨ p4) ∧ False) ∧ True)) ∧ ((p4 ∨ p2) → True)) ∧ False) ∧ (p2 ∧ p1)) ∨ False) ∧ True) ∨ ((p1 ∧ p5) → p1)) := by
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
theorem thm_5_vars_40409494964004504768885092677 : ((((((p3 → (False ∨ (((((p4 ∧ True) → (True ∨ p2)) ∧ p2) → p2) → p3))) → p2) ∧ ((True → (False ∧ True)) ∨ p3)) ∨ True) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655057897819303644301659406565 : (((((p2 ∧ (True → ((((p3 ∧ ((p1 → p5) ∨ (p4 ∨ p1))) ∨ (p2 ∧ p1)) ∨ p1) ∧ ((p5 → p3) → p2)))) → p1) ∨ (p5 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191243244621280803554634426946 : (((False ∧ False) ∧ ((p2 ∧ ((False ∨ p4) ∨ p1)) ∧ p2)) ∨ (((p2 ∧ p5) → ((True → (p3 ∧ p4)) → (p2 ∧ p1))) → (p3 → (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323468658607808353883688306190 : (p5 ∨ ((((p4 ∨ ((((True ∧ (False ∨ True)) → ((((p1 → p4) ∨ p5) ∧ p3) ∧ p3)) → p3) → p4)) → p2) ∧ p4) ∨ ((False ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175365381458261621949143305406 : ((p5 ∨ (p2 → ((p1 → True) → ((True → ((p2 ∧ (p2 ∧ p1)) ∧ True)) → p2)))) → (False ∨ (p2 → ((p5 ∧ False) ∨ (True ∨ (True ∨ p5)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251974267630082290289509054327 : ((p4 → False) ∨ (((p5 ∧ (p1 ∧ False)) ∧ ((((((p4 ∧ True) → (False → False)) ∧ (p4 ∧ p2)) ∧ (p4 ∨ False)) ∨ p5) → p2)) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199629024128510931965429840702 : (((((p1 ∧ True) ∧ False) ∨ (True ∨ p2)) → False) → ((p5 ∨ (((((p4 ∨ p1) → p5) ∨ p4) ∨ p5) ∧ (p4 ∧ (p5 → p3)))) ∧ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ True) ∧ False) ∨ (True ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∧ True) ∧ False) ∨ (True ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662010810817848594305900117036 : (((((((True ∧ p2) ∨ False) ∨ ((False → (p2 ∧ p3)) ∨ ((p4 ∨ p1) ∧ p3))) → (p1 ∨ (((p3 ∨ False) → True) ∧ True))) → (p1 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229347169884684732722722392596 : ((p1 → (False ∧ p1)) ∨ ((((p2 → p5) ∨ p4) ∨ ((p1 ∧ (p1 → p1)) ∨ (p1 ∨ (((True → ((p1 → p2) ∨ p3)) ∧ p2) → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682756415822647949583856539211 : ((((((p1 ∨ (p1 ∧ p1)) ∨ p3) → ((p1 ∨ (((p4 → (True ∨ p2)) → True) → True)) ∧ p2)) ∧ ((((False ∨ p3) → p3) ∨ True) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322428947445570047451029094744 : (p5 ∨ (((((p3 ∧ p5) ∨ p3) ∨ (True ∨ p4)) ∧ ((False ∨ ((p4 → p4) ∨ False)) ∨ ((False ∨ (p4 → p3)) ∨ (p1 → (p2 → False))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189947401192858091686435886721 : ((p4 → ((p4 ∨ (((p2 → p2) → p5) ∧ p4)) ∨ p4)) ∧ ((p3 ∨ (p3 ∨ p3)) ∨ ((p1 ∨ (False ∨ True)) ∨ ((True ∨ (True ∧ p4)) → p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52306403794481538473005796842 : ((((False ∨ ((True ∨ ((p1 → ((p4 → p1) ∧ True)) ∧ p1)) ∨ False)) ∧ p3) ∧ ((((True → (p5 → (p2 ∨ p4))) ∧ p3) → p5) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326979106878928876175537886075 : (True → ((((((p2 ∨ (True ∧ False)) ∨ (p1 ∨ (False ∧ (p2 ∨ p1)))) ∨ (p4 ∨ True)) ∧ (p2 → (p2 → True))) ∨ ((p2 → p4) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300050150500990978974805079570 : (False ∨ (((((p1 → False) → (((True → (((True → False) → (p5 → (p1 ∨ p1))) → p2)) ∧ (p1 → p3)) ∨ False)) ∧ p4) ∧ p1) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247868684397757358720411447328 : ((p1 ∨ p2) ∨ ((False → False) → (((((p3 → True) → p2) ∨ p4) ∧ ((True → False) ∧ (p4 ∧ ((p4 ∧ p1) ∧ (p5 ∧ (p1 → True)))))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h11.left
    let h15 := h11.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h17 := h6 h16
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h4.left
    let h20 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h24.left
    let h28 := h24.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h29 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h30 := h19 h29
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641558022535017177650083770208 : (((((p3 ∧ False) → (((((True ∧ p4) → True) → p5) ∧ True) ∧ ((p2 ∧ (((False ∧ False) → p1) → (p4 ∨ (p3 ∧ p3)))) → p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154722637527126903265485391198 : (((((p2 ∧ (p2 ∨ (p1 ∨ ((p4 → (p4 → True)) → p3)))) → (p5 ∧ p3)) → p5) ∨ (p2 → True)) ∧ (False → (False ∨ ((p2 ∧ p3) ∧ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112465726562734920840616660236 : ((((((p2 ∧ ((p1 → p5) ∨ True)) ∨ (p4 → p2)) ∨ (True ∧ (p2 ∧ ((False ∧ (p2 ∧ (p4 ∨ p3))) → p2)))) ∨ p4) → p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793267177683955737768477767113 : (((True → (p2 ∧ ((((((p5 ∧ True) → (((False ∧ True) ∧ p4) → True)) ∨ (p2 ∨ False)) → p4) ∨ True) ∧ (p4 ∨ ((p1 ∨ p3) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146991831212380319069367841973 : ((((False → ((((p5 ∨ (p3 → p1)) ∨ p3) ∧ (((False ∨ True) ∧ (p2 ∨ p3)) → False)) → True)) → p5) ∧ p5) ∨ (((False → p1) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263927374468023497688668680455 : (True ∧ (((p3 ∨ (p4 → p5)) → (((False ∧ True) ∧ p4) → (p1 ∨ (p5 ∨ p2)))) → ((((p5 ∨ p4) ∧ (p1 → (True → True))) ∨ p2) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351467255294799653198113626754 : (p4 → ((p3 ∧ ((p5 ∨ p4) ∧ ((((p5 → (p3 ∧ (p1 ∧ p4))) ∨ True) ∧ p5) → (p3 → (p5 ∧ p2))))) → (p2 → ((p5 ∨ p1) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148032682719375916319343013295 : (((((p2 ∨ p2) ∨ p4) → ((p3 ∨ p2) ∨ ((((True ∧ False) ∨ (p3 ∧ p4)) ∨ p2) ∧ p1))) ∨ (False ∧ p5)) ∨ (((p2 ∨ p4) ∧ p4) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55635806855210442154512591324 : (((((False → p3) ∧ p5) ∧ p3) ∧ ((p1 ∧ (p4 ∨ (((((p3 ∧ True) → (p4 ∨ False)) ∧ p1) → p5) ∧ ((p2 ∨ p2) ∧ p3)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314545495549191942395455934589 : (p3 ∨ (((((p4 → (p1 ∧ p2)) ∨ ((True ∨ p3) ∧ False)) ∧ (False ∨ p5)) ∨ ((False ∧ p3) ∨ True)) ∨ ((p4 ∧ p1) ∨ ((p3 ∨ p3) → p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54528600439877394777392056960 : ((((p1 ∨ p3) ∨ (((False ∨ False) ∧ p4) ∨ True)) ∨ ((p4 → (p2 ∧ True)) → (((p3 → (p4 ∨ p3)) ∨ ((p2 ∧ p3) ∧ p1)) ∧ p5))) ∨ p5) := by
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
theorem thm_5_vars_172501473148660458207889690207 : ((((True ∨ p3) ∧ False) ∧ (p3 ∧ ((((p1 ∧ False) ∨ p4) ∧ p3) ∧ (p1 ∨ p2)))) ∨ ((p1 → True) ∧ (((p4 ∨ (p1 ∧ True)) ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173798820487495398119540551294 : (((p1 ∧ ((p5 → (True ∧ ((p4 ∨ True) ∧ (p3 ∨ False)))) → (p3 ∨ True))) ∨ p1) → ((p2 → p5) ∨ (((p5 ∨ (True ∨ p2)) → p5) → p1))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249557970835385381057859972529 : ((p5 ∨ p2) ∨ ((((p1 ∨ (p2 ∧ p5)) ∨ p2) ∨ (False ∨ False)) ∨ ((p3 ∨ (((p4 ∧ True) ∧ True) ∧ p3)) → (True ∨ ((p5 → p3) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123806665730389562119499334366 : ((((p5 → p1) ∧ ((p5 → (p2 ∧ (((True → p5) ∧ True) ∧ p4))) → p3)) ∨ ((p1 → ((True ∨ (p1 ∨ False)) ∨ p5)) → False)) → (p2 → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337793186992231621547104714578 : (p1 → ((((((p3 ∨ (p3 → p4)) ∧ (p4 ∨ p4)) → p5) ∧ (p2 ∨ (p4 ∧ True))) → p1) → (p4 ∨ (p4 → (p4 ∧ ((p1 ∨ p2) ∨ p1)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766245716383576282312601746912 : (((p4 ∧ ((p5 ∨ False) ∨ (p1 ∧ (p4 → ((((False ∧ (False → (False ∨ (p4 ∨ p1)))) ∧ ((p4 ∨ p2) → False)) ∨ p3) ∨ (False ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185255443831480016474309057447 : ((p1 ∧ (((True ∨ ((p1 → p2) ∧ p2)) → p1) ∧ (p5 → True))) ∨ (p4 → (False → ((p3 ∧ ((p5 ∧ (p1 ∧ p3)) → (False ∨ p5))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117626490005570420781638073296 : ((p3 ∧ ((p4 → (False ∧ ((((p2 → (False → True)) → p1) ∧ ((((p2 ∨ (False ∧ p1)) ∨ False) ∧ p4) ∧ True)) → p3))) ∧ p2)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57890891891123359638813066055 : (((p3 ∨ (False ∧ p4)) → (((False ∨ p5) → ((True → (((((p2 ∨ p1) ∧ p3) ∧ False) ∧ True) ∨ (True → p4))) ∨ (p4 ∨ p3))) ∨ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688555515028383536016900906587 : ((((p1 ∨ ((p5 → False) ∨ ((p3 → (p1 → (p1 ∨ (p2 ∨ p4)))) ∧ (p1 ∨ p1)))) ∧ ((p3 ∨ ((p5 ∨ (p2 ∨ p1)) → p3)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264064306213580977891847015872 : (True ∧ (((((p4 ∧ p1) ∨ (p2 ∧ (True ∨ False))) → p3) → p1) ∨ ((((p5 ∧ p5) → p4) → (True ∧ True)) ∨ (p2 → (p1 → (p4 ∨ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124299532322264142482556010102 : (((((p1 ∨ True) → (p3 ∨ True)) ∧ (p1 ∧ True)) ∧ (p1 ∧ (p3 ∧ (p4 ∧ ((p1 ∨ (p4 ∨ (p3 ∨ (p2 → True)))) ∨ p4))))) → (p5 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300541550765452076879474288096 : (False ∨ ((((((p2 → (((True ∧ True) ∧ p2) ∧ True)) → p5) ∨ p3) ∨ (p5 ∧ (p1 → (p5 ∨ p1)))) → p1) ∨ (((p2 ∧ True) → True) ∨ False))) := by
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
theorem thm_5_vars_56809411268439064928420325073 : ((((p3 ∨ p5) → True) ∧ (((p2 → p1) ∨ True) ∧ ((p2 ∨ p2) → ((p5 ∨ (p5 ∧ p3)) ∨ ((p3 → (p1 ∧ (p3 → p3))) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299227924455247510561293090678 : (False ∨ (((((p5 ∧ p1) ∧ p4) ∨ (((p4 ∨ (p2 → (p5 → False))) → p3) ∧ (((p3 ∨ p3) → (p4 → p1)) ∧ p1))) → (p5 → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167713000562610980872438481578 : (((p5 ∨ ((p2 ∨ (p1 ∧ ((p3 ∧ p1) → p3))) ∧ (p3 → p4))) ∧ (p2 ∧ (p4 → False))) → (((True ∧ p2) ∨ p4) → (p4 ∨ (p3 → True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h7.left
        let h17 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h7.left
        let h23 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h1.left
    let h27 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h27.left
        let h37 := h27.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h38
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- Conjunctions on the left can always be decomposed.
        let h42 := h27.left
        let h43 := h27.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h44
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255925488323815075699264043950 : ((True ∨ p2) → ((p4 ∧ (((False → p1) ∧ ((p5 → False) ∧ ((p5 → ((p1 → (p5 ∧ p1)) ∧ p1)) ∨ p1))) ∧ False)) ∨ ((False → p5) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650129915230352468176533039261 : ((((((((False ∨ ((p3 ∧ p2) → (p4 → False))) → (p5 ∨ p2)) ∨ (p3 ∧ p3)) → False) ∧ ((p1 → (p4 ∨ p3)) ∧ True)) ∧ (p3 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325885812369557467298126439627 : (p5 ∨ (p4 ∨ ((p5 ∨ (p3 ∨ p5)) ∨ ((False ∧ (((p5 → ((p3 → (p4 ∨ p2)) ∧ True)) ∧ p5) ∨ ((p2 ∧ (p1 ∧ p4)) → p2))) → False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249485178676131385304019247272 : ((p5 ∨ p1) ∨ ((((p2 ∨ (((((p4 ∧ ((p1 → p1) → (p1 → p2))) ∨ p3) → False) → p1) ∨ p5)) ∨ (p3 ∨ p3)) ∨ True) → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
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
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135605405575297090519548510298 : ((((p4 ∨ p1) ∨ (p1 ∧ (((p2 ∨ (p1 ∧ p1)) → (p4 ∧ False)) ∧ (p3 ∨ False)))) ∨ (((False ∧ True) ∧ p4) → False)) ∨ ((p2 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171607894792402149926330090310 : ((((((p1 ∨ p2) ∨ p4) ∨ True) ∧ (p5 ∧ (((p3 → False) ∨ True) → True))) ∨ p3) ∨ ((True ∨ ((p3 → p3) → ((True ∨ p3) ∧ p5))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



