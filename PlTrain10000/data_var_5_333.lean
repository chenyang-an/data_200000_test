variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693352036538944230388696240373 : ((((False → (True → ((p2 → (p1 ∧ (p1 ∨ (p4 → p2)))) → (p1 → p2)))) ∧ ((((p2 ∧ p3) ∧ (p5 ∨ False)) ∨ (p4 ∨ False)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305403720181541303927643892872 : (p1 ∨ (((((p3 ∨ p2) ∨ (p1 → True)) → ((True ∨ (p4 ∧ p1)) ∧ p2)) → (p2 ∧ p4)) ∨ ((((p5 → p1) ∨ p1) ∧ False) → (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165288227966504197317938608434 : ((((((p1 → p3) ∧ (p2 ∧ p4)) ∧ False) → (((True ∧ p2) → p1) ∧ p3)) → (p2 ∧ p3)) ∨ ((p2 ∧ p3) ∨ (((True → True) ∨ p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216884804843378335338561402891 : (((p2 ∨ (True ∨ False)) ∧ p3) → (((True ∧ (p4 ∨ ((((p4 ∧ (p3 ∨ p2)) → p1) ∧ ((p1 → p3) → True)) ∨ (p1 → p4)))) ∧ False) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310728454583561206810070010267 : (p2 ∨ (((p2 → p3) → True) ∧ ((((p4 ∨ p3) → (p3 ∧ p4)) → ((False → False) → False)) ∨ (((p2 ∧ True) ∧ p3) → ((True ∨ False) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171789074870019692989943413297 : (((((((p4 ∨ p1) ∧ (p4 → (False ∨ p3))) ∨ p2) ∨ p5) → (p4 → False)) → p3) ∨ (((p4 ∧ p3) ∧ (((p4 → p1) ∨ p1) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260779576796021028738794961908 : ((p3 → p5) → (((((((p4 ∧ p1) ∨ ((((p2 → p5) ∨ p1) → (p5 ∧ p4)) ∨ p5)) ∨ True) ∨ p4) ∨ p3) ∧ (True ∧ False)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147980892453759018381433491471 : ((((((p1 → p1) ∨ p3) → ((((False ∨ p1) ∨ (p2 ∧ p3)) ∧ (p3 ∧ p4)) ∨ True)) ∧ True) ∨ (p2 ∨ True)) ∨ ((p3 ∨ True) ∧ (p1 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52081352525279018574379990005 : ((((p3 ∨ ((p2 ∧ ((p2 ∧ p3) ∧ ((False ∧ p4) ∧ p3))) → (True → p4))) ∧ p3) → ((p5 ∨ p5) ∧ (p5 ∧ ((p2 ∨ False) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353470227698793378624333641101 : (p4 → (p2 ∨ (((((p1 ∧ (((((p2 → (p1 ∨ (False → p3))) ∧ p5) ∨ (p3 ∨ True)) → (p1 ∧ True)) ∨ True)) ∨ p5) ∨ p2) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134928298200564828552710628053 : ((((((p5 ∨ ((p5 → True) → ((p1 ∨ False) → (p3 ∧ False)))) → p3) ∧ ((p4 ∧ False) ∨ True)) → p2) ∧ (p4 ∧ False)) ∨ (p2 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668932787715674521467015354788 : (((((False ∨ ((True ∧ (p5 ∧ (p2 ∨ ((p2 ∧ p2) ∨ (p4 ∨ (p2 ∧ True)))))) ∨ (p4 ∨ (p3 ∨ p5)))) ∨ False) ∨ ((p1 ∧ p2) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_168297627278071104377772109961 : (((p1 ∨ p1) ∧ (((p5 ∨ p3) ∨ (True ∨ ((p4 → p4) → (True → p2)))) → (p5 ∧ p3))) → ((p1 ∧ ((False → p5) ∨ p1)) ∧ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
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
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : ((p5 ∨ p3) ∨ (True ∨ ((p4 → p4) → (True → p2)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h17 : ((p5 ∨ p3) ∨ (True ∨ ((p4 → p4) → (True → p2)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h18 := h11 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160079097664865947355123194691 : (((False ∨ ((p2 → p1) ∨ ((p1 ∨ p1) → (((((True ∧ True) → False) ∧ p5) → True) → p3)))) → p2) → (((p4 → (p3 → False)) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_160960385303455236337578720243 : ((((False → p2) → p1) ∧ ((p4 → (p1 ∧ p2)) → (p4 ∨ (p1 ∨ (((p2 → p4) → p4) → p5))))) → (((False → (p1 ∧ False)) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (False → (p1 ∧ False)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245246287129438817449352457289 : ((p2 ∧ p1) ∨ (((True → p3) → ((False ∨ p1) ∨ (p4 ∧ True))) ∨ ((p3 ∨ ((p5 ∨ p4) → p1)) ∨ ((p1 → p1) ∨ ((False ∨ False) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176914324145146652424676600912 : (((p2 ∨ True) ∨ ((True ∧ (((p3 → (p5 → True)) ∧ p4) → p4)) ∨ p4)) ∧ ((p3 ∧ ((p1 ∨ p1) → p4)) → (p5 → ((True → p1) → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244949944539377858332468606003 : ((p1 ∧ p3) ∨ ((True ∨ p3) ∧ ((p3 ∧ (((p3 → ((p3 ∧ True) ∧ p5)) ∧ ((p5 ∧ p5) ∧ p1)) ∧ (p3 ∧ p5))) ∨ ((p3 → True) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792155143533022359575709758282 : (((True → (((False ∨ (p4 ∨ True)) ∧ (((((False → p3) ∧ p4) ∧ p2) → ((False ∨ (p1 ∧ p1)) ∨ p1)) → p4)) → ((p5 ∨ p3) ∨ True))) ∨ p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112799478428526759795641082316 : ((((p5 → (False ∨ ((p2 ∧ p4) ∧ p1))) ∧ ((p1 → (True → True)) → (((p4 ∧ ((p2 ∨ p3) → p2)) ∨ p3) ∨ p1))) → p1) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58839824319016208475532815234 : (((True ∧ p1) ∨ (((p5 ∨ (p4 ∨ ((p5 ∨ p5) → (((False ∧ p1) ∧ p2) → p5)))) ∧ ((p5 ∨ (p3 → p4)) ∨ False)) ∨ (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186020223960571247531249279496 : (((p4 → ((True ∧ ((p5 → p4) → (p2 ∧ True))) → False)) ∧ p1) → ((((False ∧ (((p5 ∨ p5) → (p3 ∧ p1)) → p2)) ∨ p4) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_142848501765457722765463593014 : ((p4 ∨ (((((p4 ∨ p1) ∨ (p2 ∧ p3)) → (True → ((p5 ∧ (p5 ∧ False)) ∨ (p3 ∨ p4)))) ∨ (p2 → True)) → False)) → ((True → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686582738331019341700450600542 : (((((p5 → p4) ∧ (((p4 → (p2 → (p5 ∨ p2))) → (((False ∧ p1) ∨ p1) → p3)) → False)) → (p5 ∨ ((p5 → p4) ∨ (p3 ∨ p3)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606161324025786268022031912331 : (((((((True ∧ ((p2 ∧ ((((True → (p2 ∨ (True ∧ (p3 → p4)))) → p1) → p3) → p1)) ∨ (True → False))) → p1) ∧ p5) ∧ p3) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624161688487771445147663704583 : ((((p2 ∨ (p5 ∨ (((True ∧ (p1 ∧ p5)) → (((p2 ∨ p5) ∧ (p4 → p1)) → (p2 → (((p1 ∧ True) ∨ p1) ∨ p3)))) → False))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112566523244961819018535793481 : ((((True ∨ ((((True ∧ p4) ∧ False) ∧ p5) ∧ ((p3 ∨ (p3 ∨ (p4 ∨ (p1 ∧ (p2 → p4))))) ∧ (p5 ∧ p4)))) → p5) → p3) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190096597559814399616048133272 : ((((p3 ∧ (p1 ∧ (True ∧ False))) ∨ (False ∧ p1)) ∧ p1) ∨ ((False → (p3 ∨ (True ∧ (p1 ∨ False)))) ∨ ((False ∨ (p3 ∨ (True ∧ p1))) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326916340490774071566729369701 : (True → ((((p3 ∨ (p3 → (((p5 ∨ p2) ∨ (True ∧ ((p2 ∨ p1) ∨ True))) ∨ p5))) → (p1 ∨ ((p4 ∨ (p3 → p4)) ∧ p1))) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198616614642453072295122613822 : ((p2 ∨ (p5 ∧ ((p4 ∧ p2) ∧ (p2 ∨ True)))) ∨ (p2 → (((p5 ∨ (False ∧ p5)) ∨ False) → (((p1 → False) ∧ (p2 ∧ False)) → (p2 ∧ p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62453308851752284849054933674 : ((p3 ∧ ((p5 ∨ (p1 → p3)) → (((p1 ∧ p5) → (((p3 ∧ (p5 ∨ (p1 → p4))) → (False → p3)) ∧ ((True ∨ p4) → p5))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157741863882357814057295748976 : (((((p4 ∨ ((p4 ∨ True) → (p5 → p2))) ∧ (False ∨ p1)) ∨ p3) ∧ (p2 ∨ (p4 → (p2 ∨ p1)))) ∨ (p5 ∨ ((p3 ∧ p2) ∨ (p3 → True)))) := by
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
theorem thm_5_vars_43393020352747166148980788058 : (((((p4 ∨ ((p1 → (((p1 ∨ p4) → ((p1 ∨ p2) → p2)) ∨ (p1 ∨ False))) ∨ True)) → (p5 ∧ ((p1 → p3) → p3))) ∨ p3) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_516068403997125282203378580676 : ((((p2 → p3) ∨ (((((p5 ∧ p4) → (((p1 → p2) ∨ p2) → (p2 ∧ (p5 ∨ True)))) ∨ p2) ∧ ((p1 → (p5 ∧ True)) ∧ p5)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174925502023431934059217508392 : (((p5 ∨ p5) → (((p1 ∧ (p2 → (p1 ∧ False))) ∧ True) ∨ ((p3 ∧ p5) ∧ p2))) → ((p2 ∧ ((p5 → False) ∨ False)) ∨ ((False ∧ True) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345285246467034623566014783309 : (p3 → ((p1 → ((((((False ∨ False) ∧ ((p2 ∨ p1) → p2)) → p3) → ((p1 → (p3 ∧ p5)) ∨ True)) → (p2 ∧ p5)) ∨ (p2 ∨ True))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152207583245157343330173447057 : ((((p2 ∧ ((p2 ∨ p2) → False)) ∨ True) ∧ ((((((p2 → p4) ∧ p3) ∨ p4) ∧ p3) ∨ p5) → (p4 ∧ p5))) → (((p5 ∧ p2) → p1) ∨ True)) := by
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
theorem thm_5_vars_46484871723762689193323930478 : ((((p1 ∧ (p1 ∧ p4)) ∨ ((p3 → (p5 ∨ p2)) ∨ (((p1 ∧ p4) ∨ (((p5 ∨ p4) → p5) → False)) → (True → p2)))) ∧ (p4 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769014899143562474008326667835 : (((p5 ∧ (((p3 → p3) ∧ p5) ∨ ((p5 → (False ∧ ((p3 ∧ ((p1 ∧ p5) ∨ (p3 → ((p2 → (False → p2)) ∨ False)))) ∨ p3))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167623303366699512471662312931 : ((((True → (((p5 ∨ p2) ∨ p4) ∧ (False ∧ (p1 ∧ (p5 → p2))))) ∨ False) → (p3 ∧ p1)) → ((p1 ∨ (p2 → (p4 ∨ (False → False)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173815690087318451237595739839 : (((False ∨ ((((p1 ∨ False) ∧ ((False ∧ p1) ∧ (p1 ∧ p4))) → True) ∧ True)) ∨ p1) → ((((True ∧ (p1 ∧ (p5 → p3))) ∧ p5) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
theorem thm_5_vars_161022057158670902018201001974 : (((True → (p5 ∧ p1)) ∨ ((((p2 ∧ (p4 → (p2 ∧ p5))) ∧ True) → (p4 → (p5 ∧ True))) → p1)) → (p3 ∨ (p4 → ((p5 → p1) ∨ p5)))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (((p2 ∧ (p4 → (p2 ∧ p5))) ∧ True) → (p4 → (p5 ∧ True))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h17 := h7 h10
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45917913333621331933668439128 : (((p4 → (((False ∧ False) ∧ p1) ∧ (p4 ∨ (((p2 ∧ True) ∧ True) → (p2 → (p1 → (p3 → (p5 ∨ (p1 → (p5 → p5)))))))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343665931368625940325030091225 : (p2 → (True ∧ (p5 ∨ ((((p1 ∧ p5) → p2) → p4) → (p3 ∨ (((p4 → False) ∧ (((p3 ∨ p4) → p5) ∨ (p2 ∨ (p1 ∨ p4)))) → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : ((p1 ∧ p5) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h7
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : p4 := by
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : ((p1 ∧ p5) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h21 := h2 h17
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h16
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h25 : p4 := by
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h26 : ((p1 ∧ p5) → p2) := by
            -- Implications on the right can always be decomposed.
            intro h27
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h30 := h2 h26
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h31 := h4 h25
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h33 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h34 := h4 h33
        -- False on the left can always be used.
        apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66636749036544689860206408556 : ((True → (((False ∨ (p5 ∧ True)) ∨ (((p2 ∧ p4) ∨ p1) ∨ (p4 → p2))) ∧ ((((True → False) ∨ ((p1 ∧ False) ∧ p3)) → False) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177932653337802592080594055105 : ((((p5 ∧ (p5 ∧ (p3 ∧ p2))) ∨ (p4 ∨ ((p4 → p3) ∧ p2))) ∨ p1) ∨ ((p4 ∧ p1) ∨ ((False ∧ False) → ((True ∧ (p2 → p4)) → p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110871530948006732769215051787 : (((((p1 → (p4 ∧ ((((p1 → (((p4 ∨ False) ∨ ((p5 → False) ∧ p5)) ∧ True)) ∨ True) ∨ p3) ∨ p5))) → p3) → p3) ∧ p5) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180160755321464349032617170992 : (((((p4 → ((p1 → True) ∧ p2)) ∧ (p2 ∧ p2)) → (True → p3)) → p4) → (p3 → ((((True ∨ True) ∨ (p4 ∧ (p2 ∨ p1))) ∨ p1) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 → ((p1 → True) ∧ p2)) ∧ (p2 ∧ p2)) → (True → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64056456418841072201209161009 : ((False ∨ (((((p4 ∨ (p1 ∧ (p5 ∧ ((p5 ∨ p2) ∧ p1)))) ∨ (p4 ∨ p3)) → p4) ∧ (p5 ∨ p4)) ∨ ((False → (p2 → p3)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308701362631382923776934212947 : (p2 ∨ ((p3 ∨ (p1 → (((p2 ∧ ((p3 → p3) → ((p3 ∨ p5) ∨ (p1 ∧ p4)))) ∨ (False → (False → p3))) ∨ ((p2 → p4) ∧ p5)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178457743634920525693698371138 : (((p3 ∧ (p2 ∨ (p3 → ((p2 ∨ True) ∧ False)))) ∧ ((False ∧ p2) ∧ p4)) ∨ (((((True → p2) → False) → (p4 ∨ (p5 ∨ p5))) ∧ False) → p1)) := by
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
theorem thm_5_vars_119858720135549048415135120750 : (((((((((((p3 → p4) → p1) ∧ p5) → p2) ∨ (True ∧ ((False ∧ p1) ∧ p1))) ∧ p4) ∧ p2) → True) ∧ (p1 → p5)) ∧ p4) → (p2 → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175873088057329243880677883682 : ((((True → (False ∧ ((p3 ∨ p5) ∨ p3))) ∨ (p1 ∧ (p5 ∨ p2))) ∨ True) ∧ (((p4 ∧ (((p5 ∨ p4) ∧ p3) ∨ p5)) ∧ True) → (p4 ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227110153981198850829050202424 : (((p4 ∨ p1) → p2) ∨ (((p1 → (False ∧ (((p4 ∨ p5) ∧ (True ∧ (False → p3))) → (p1 ∧ (p2 ∨ p4))))) ∨ p3) ∨ ((p5 → p5) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34029914889492828535061618989 : ((p5 ∨ (p5 ∨ (p1 ∨ ((((p3 → p3) → ((p1 ∨ p4) → ((p3 ∧ p4) → ((True ∨ False) ∨ (p2 ∨ p4))))) ∧ (p1 ∧ False)) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700776035590464351078787738064 : (((((((p5 → p2) ∧ p4) ∨ ((p4 ∨ False) ∧ p3)) ∧ p1) ∧ ((p5 ∨ ((p3 → p4) ∨ (p3 ∨ (p3 → ((True ∨ False) ∧ p3))))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208222062339890856452939002139 : (((p5 → (p4 → False)) → (p3 ∧ p3)) → ((p2 ∨ (((((False ∨ p5) → p4) ∨ False) ∧ (((p3 ∧ (p5 ∨ p2)) → True) → p2)) ∨ True)) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729514749602794371216296480401 : (((((p1 ∨ p4) ∨ True) → (((p2 ∨ p2) ∧ p2) ∨ ((((p4 → False) → True) → (p2 → (p4 ∧ (((p2 ∧ p3) ∨ p2) ∧ p3)))) → True))) ∨ p3) ∧ True) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136452495648670441379836090449 : (((p1 ∨ (True ∨ (False → p1))) → ((((p5 ∨ ((p5 → p5) ∨ True)) ∧ (False → (p4 ∨ p1))) ∧ False) ∧ (p1 → p1))) ∨ (p1 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40506228280906997416441510808 : ((((p1 ∧ (p5 ∨ ((((p3 ∨ p3) → ((p2 ∧ ((((p4 ∧ True) ∨ p1) → (False ∧ p3)) → True)) ∧ p2)) ∧ p3) → p5))) ∨ True) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622595965336207609002907318402 : ((((p4 ∧ ((((True ∧ ((p1 ∨ p5) ∧ (((p4 → True) ∧ (p2 → p4)) ∧ False))) → (p3 ∧ (p3 ∧ p4))) ∧ (False → p4)) → p4)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634640508731149847619674480212 : (((((p2 → (((((False ∨ p1) ∨ ((True ∨ p1) → (p1 → False))) → ((p2 ∨ p1) ∨ p5)) ∨ p2) ∧ p2)) ∧ (False ∨ (p2 → p5))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198384220934291357389504680130 : ((p3 ∧ ((False → False) ∧ ((False → True) ∧ p2))) ∨ (p5 → (((p1 ∧ False) ∧ (((True ∧ (((p5 → False) ∧ p1) ∨ p5)) ∧ p5) ∨ False)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313968652249849507605444752825 : (p3 ∨ (((False ∨ ((False ∨ (((p4 ∧ (p5 → (True → p2))) ∧ p5) → False)) ∧ (p1 → p5))) ∨ ((True ∧ (True ∨ p2)) ∨ True)) ∨ (True ∧ p3))) := by
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
theorem thm_5_vars_160356435957229047175319869018 : ((((((True ∧ True) → (True ∨ (p2 ∨ ((True ∧ True) ∨ p2)))) → p2) ∨ p2) ∧ (p5 → (False ∧ p3))) → (p1 ∨ (p2 ∨ (p2 ∨ (False ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∧ True) → (True ∨ (p2 ∨ ((True ∧ True) ∨ p2)))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172856913729730732681639107916 : ((False ∧ (p2 ∧ ((True ∨ ((p1 ∨ p1) ∨ ((p3 ∧ p2) ∧ p3))) ∧ (p2 ∧ p4)))) ∨ (p4 → ((p1 ∨ True) ∨ (p4 → (True ∧ (p5 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114702977352417046329174300044 : (((((p4 ∧ ((p5 ∨ (True ∧ (p4 ∧ ((p1 ∨ p3) ∧ p4)))) → p4)) ∨ p1) ∨ p5) → ((True ∨ ((p3 → p4) → True)) → p4)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92610813927577898800714498596 : (((False → False) → (((p2 ∨ (((True ∧ (p2 → p4)) → ((False → False) → True)) ∧ (((False ∧ p5) ∧ True) → (p2 ∨ p2)))) ∧ True) ∧ False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258982260390903875498453524706 : ((True → p3) → ((False → p4) → ((((((p3 ∨ False) ∨ p3) ∨ (p5 → (p1 → p4))) ∧ p1) → ((p2 ∨ (p2 ∨ True)) ∨ p4)) ∨ (p2 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234947656269125679402707848198 : ((True ∧ True) ∧ (p2 → ((((p5 ∧ ((p5 ∨ ((False ∨ p5) ∧ (False ∧ p2))) ∨ ((p1 ∨ p3) → p1))) ∨ p4) ∨ True) ∨ ((False → p5) ∧ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113847994871624933022154515015 : (((p5 ∨ (p1 → ((p3 ∨ (False → True)) ∧ (((False → (True → False)) → (p5 ∨ False)) → ((False ∧ p5) ∨ p5))))) → (p2 → False)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358607744298725262067752122992 : (p5 → (p3 → (((False ∨ p3) ∧ ((p4 → p1) ∨ p3)) → (((p2 ∧ (p3 → p1)) ∨ ((p3 ∧ (p3 ∧ (p5 → (p1 ∧ p1)))) ∨ p4)) ∨ p5)))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248159221882824652487543045470 : ((p2 ∨ False) ∨ ((p4 ∨ (p1 ∧ ((p5 ∨ ((p1 → True) ∧ (p3 ∧ True))) → False))) → (((p5 ∨ p4) ∧ (p5 → False)) ∨ (p3 → (False → p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38218947820207396766864207756 : (((((p2 ∧ p5) ∧ (p4 ∧ ((((False ∧ True) ∨ p1) ∨ p5) ∧ (((p5 ∨ False) → p5) ∨ (p4 ∧ p4))))) → ((True ∨ p2) → p3)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47043629775914336050966992596 : (((((p3 ∨ (False → (p3 → p4))) ∨ ((((p1 ∧ p2) ∨ p4) ∧ ((True → p2) ∨ (p4 ∧ p4))) → p4)) ∧ (p5 ∨ p1)) ∨ (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769154645860272048297215179374 : (((p5 ∧ ((p1 → True) ∧ (((p1 ∨ p2) ∨ (p3 ∧ (p5 ∨ ((p4 ∧ ((p1 → p3) ∧ p4)) ∧ False)))) ∨ (p4 ∧ ((p1 ∧ False) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156691433544467035911263111699 : ((((((p4 ∨ (p2 → p5)) → (p3 ∧ p3)) ∨ (True ∧ (p2 ∨ p3))) ∧ (p2 ∧ (p1 ∨ p1))) ∧ p3) ∨ (((False ∨ p3) ∨ (True ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641847356433081356922099315608 : (((((False → p2) → ((((((True ∨ ((p1 → (p5 ∨ p3)) ∨ p1)) ∧ p4) → p5) ∨ (True ∨ (p5 ∨ True))) ∧ False) ∧ (p2 ∨ p1))) → p4) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77251911244074114915149214589 : (((((p5 ∨ True) → False) → (False ∨ (((True → p2) ∧ (False → p1)) → (p3 ∧ (False ∧ (((True → (p5 ∧ False)) ∨ p2) → False)))))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ True) → False) → (False ∨ (((True → p2) ∧ (False → p1)) → (p3 ∧ (False ∧ (((True → (p5 ∧ False)) ∨ p2) → False)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618586710978667227573996076480 : (((((p4 ∨ ((p4 → p1) ∧ p3)) → ((p1 ∨ (p4 ∧ ((p4 → ((p5 ∨ p1) ∧ (False ∨ (False ∧ p2)))) ∧ (p4 → p4)))) ∧ True)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51281045678948197670929021210 : (((p1 ∧ (p3 → (p4 ∧ (((((p4 ∧ (p1 → p3)) ∧ p5) → (True → p5)) → p2) ∧ p1)))) ∨ (((p3 ∨ p1) → (p5 ∨ p1)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346933611948087428101070071799 : (p3 → ((((p1 ∨ (((True ∧ ((True ∨ p2) ∧ p5)) → ((p3 → p3) → p4)) ∨ p1)) ∨ True) ∨ p5) → ((((p1 → p5) → False) ∧ p5) → p1))) := by
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
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h11 : (p1 → p5) := by
            -- Implications on the right can always be decomposed.
            intro h12
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h13 := h4 h11
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : (p1 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h16
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : (p1 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h22 := h4 h20
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205003708280676544909508376876 : (((False ∨ ((p4 → p1) ∨ p1)) → p4) ∨ (((p3 → ((p2 ∨ p5) ∧ (p4 ∧ (p2 ∧ p3)))) ∧ (p1 ∧ (p5 → (p4 → (p2 → False))))) → p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678884793935680326638691581933 : ((((p2 ∧ ((p5 → ((p4 → (False ∧ ((False → ((p4 → p3) ∨ p3)) → p1))) → False)) → (p4 ∧ p3))) ∨ (True ∨ (p2 ∨ (p3 → p4)))) ∨ p1) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302983622728337942864470198726 : (False ∨ (p1 → (((True ∧ (((p1 → (((p2 ∨ True) → (p4 ∨ False)) ∨ p5)) ∨ False) ∨ p1)) → ((p5 ∧ p2) ∧ (p4 ∨ (p3 ∧ p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208732172273835272161087426946 : ((p1 ∧ ((True → p1) ∨ (p5 → p5))) → ((((False ∨ p1) → (False ∨ (p3 ∧ p2))) ∨ ((p2 → (p2 ∨ p1)) → ((p5 ∧ p3) ∧ p4))) → p3)) := by
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
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (False ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (False ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h24 : (p2 → (p2 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h26 := h20 h24
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h30 : (p2 → (p2 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h31
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h32 := h20 h30
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- We need to get the right conjuct of h33 based on <expert-advice>.
      let h34 := h33.right
      -- One of the premise coincides with the conclusion.
      exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61347942461596582056420349600 : ((p1 ∧ ((((p2 ∧ ((p3 ∧ p1) ∨ p1)) ∧ ((p1 ∧ p5) → ((False ∨ p4) → False))) ∨ (p5 ∨ (p4 → (p4 ∧ (p5 → p1))))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157954641584012600228745647223 : (((((True ∨ ((p5 ∧ True) ∧ False)) ∧ p4) ∨ p4) ∨ ((((p1 ∨ True) ∨ p2) ∧ True) → (False ∨ p3))) ∨ ((p1 → p3) → ((p4 ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37408396005027829481978804176 : ((((((((p2 → ((p3 → p4) ∨ ((True → p4) → p3))) ∧ (False ∧ (p2 ∨ True))) → True) → (p1 → p4)) ∨ (p1 ∧ False)) ∨ p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164638981297535386482624156809 : (((p3 ∨ (p2 → ((p1 → p5) → (p3 ∨ (((p2 ∨ p4) ∧ p1) ∧ (False ∨ p3)))))) ∧ p2) ∨ (((p1 ∨ (p5 → p1)) ∧ p3) → (p3 ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119460215653751470667075146386 : ((p4 → ((p5 ∧ (True ∨ True)) ∨ (p2 → (p5 → (True ∧ (((p2 → (((True ∧ True) → (p4 ∧ True)) → False)) ∧ False) ∨ p3)))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219126484491170459063370106805 : ((True ∨ (p4 ∧ (p2 ∧ p3))) → ((p3 ∧ (p2 ∨ (((p3 → p2) ∧ False) → True))) → (False ∨ (((p2 ∨ p2) ∨ (True ∨ p3)) ∨ (p1 ∧ p4))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
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
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40492646340595448636697697413 : (((((p4 ∨ p2) → (((((p1 ∨ p4) ∨ ((p4 ∨ (p1 → p4)) ∨ (p1 ∨ False))) ∧ p2) → p2) → (p2 ∧ (p3 ∨ p5)))) ∨ p2) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234875078750244584572976124747 : ((p5 → (p3 → p1)) → (((p2 ∨ True) ∧ p5) → ((p3 ∨ (p4 ∨ ((p1 ∧ (False → ((p5 ∧ p2) → p1))) ∧ p3))) → (p3 → (False ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h2.left
      let h13 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h2.left
      let h22 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2458262375806050694478548282 : (((False ∧ (((True ∧ p5) → False) ∨ False)) ∨ (p4 ∧ p1)) ∨ (((p5 ∨ (p3 → False)) ∧ (p2 ∧ (p2 ∨ (p1 ∨ p3)))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173157479401053110909774144371 : ((p3 ∨ (p3 ∧ ((p4 ∧ (p1 ∨ True)) ∨ (False ∨ (p5 → ((False ∨ True) ∨ True)))))) ∨ (((p4 ∨ (True → True)) → True) ∨ ((p1 → p4) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46093369472454640441772794498 : (((((((p5 → p4) → False) ∨ False) ∧ (p1 ∨ (p5 → ((p1 ∨ p3) → ((p2 → p4) ∨ (p4 → (p1 → False))))))) ∨ p4) ∧ (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161935638232107747040680807901 : ((p1 → (p4 → ((p2 ∨ p5) ∨ (p1 ∨ (p4 ∨ ((p3 → (p2 → p1)) → ((True ∨ False) ∧ p3))))))) → (((p3 ∧ p5) → False) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158897921235504282973804886688 : ((p1 ∨ ((((True → p2) ∧ (((p4 ∨ p4) ∨ (p1 → ((p2 ∨ p4) → p1))) → False)) ∨ p3) → p1)) ∨ (True ∨ ((p2 ∧ (p3 → p4)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164955498968435255708255079113 : ((((False ∧ (((p2 ∨ True) → (p5 ∧ ((False ∧ (p2 ∨ p3)) ∨ p5))) ∨ False)) → p2) → p5) ∨ (((p3 ∧ p1) ∧ (p5 ∨ (p4 ∨ True))) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4



