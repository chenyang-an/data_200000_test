variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158140017054349022875623763153 : ((((p4 ∧ p3) ∧ (p3 ∨ p5)) ∨ ((p4 ∧ (True → (((p4 ∧ False) → p2) ∨ (p1 → p2)))) ∨ True)) ∨ ((p2 ∧ False) ∧ ((p5 → p3) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50324755138904509475669392116 : (((((((p5 ∨ p1) ∧ (p3 ∨ p1)) ∧ (p5 → p4)) → p5) → ((False ∨ p5) ∧ (p1 ∨ (p4 → True)))) ∨ ((p5 ∧ (False ∧ False)) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171583890503168848462521177432 : ((((p4 ∨ ((True ∨ p5) → (((p3 ∨ True) → True) ∧ p1))) → (p1 → False)) ∨ p2) ∨ (p3 → ((p1 → (p3 ∨ (p2 → False))) ∨ (p2 ∨ p3)))) := by
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
theorem thm_5_vars_52877279397847918730630957741 : (((p5 ∧ (p2 → (p3 ∨ (((p3 ∨ ((p4 → True) ∨ p2)) ∨ False) ∧ p2)))) → ((p3 → (True ∧ (p2 ∨ (p4 ∧ (p3 ∧ p3))))) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_115398509342073317505188347738 : (((p4 ∧ (((False ∧ (p1 ∨ p5)) ∨ p2) ∨ p4)) ∧ (False ∧ (((p4 → ((p5 → (p2 ∧ (p2 ∧ p1))) ∨ p2)) ∨ p2) ∨ p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252892964635456367837541811192 : ((True ∧ p1) → ((p4 ∨ (False ∧ (((p1 ∨ p1) → ((False ∨ p5) ∨ (True ∧ (p2 ∧ p4)))) → p4))) ∨ ((p1 → (p5 ∨ False)) ∨ (p3 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653767819540516606882123907152 : ((((((((p3 ∧ (True ∧ (p5 ∨ (p4 → p2)))) ∧ (((p3 ∨ p4) ∨ p5) ∧ p4)) ∨ p2) ∨ (p1 ∧ (p1 ∧ p2))) ∧ p2) ∨ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351632001896257949371833491586 : (p4 → (((((False ∨ (False → (p3 → ((p5 ∨ p1) → p2)))) ∨ False) → False) ∧ (False ∨ p4)) ∨ ((((p3 ∨ True) → (False ∧ True)) ∧ p3) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319492609721850957054467131561 : (p4 ∨ (((p4 → False) ∧ (p4 ∧ (((p4 → p5) → (p3 → p1)) → True))) → ((((p4 ∨ p5) ∧ False) → p2) → ((p1 ∨ (True ∨ p4)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h18 := h13 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h24 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h25 := h20 h24
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699417864728991458301192296369 : ((((((((p2 ∨ p2) → (True → (True → p1))) → p5) ∧ p4) ∨ p1) → (((p4 ∧ (p5 ∧ (True → p4))) ∨ (True ∧ False)) ∨ (False → p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45762646060600617010797558890 : (((False → ((False ∨ False) ∧ (((((True ∧ False) ∨ ((True ∨ True) → True)) ∧ p1) → p3) ∨ (((False ∧ (p1 → False)) ∧ p1) → p3)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629778178948765489178599399497 : ((((((((p4 → p3) ∧ p2) → (False ∧ (p5 ∧ ((False ∧ False) ∧ False)))) ∧ ((((p5 → p1) → p3) ∨ (p4 → p1)) → p5)) ∨ p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137509465183417889508436981561 : ((p5 ∧ ((True → ((p1 → (p4 → (True → (p4 ∨ p2)))) ∧ p1)) ∧ (((False ∧ (p4 ∧ (p2 ∧ p4))) ∧ p4) ∨ p1))) ∨ ((True ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609468504508301712989858350879 : (((((False ∧ (((((p3 ∧ (p4 → True)) ∨ ((True ∨ ((p2 ∨ p5) → True)) ∨ p5)) → p3) ∧ p1) → ((p1 → p5) → p4))) ∨ True) ∨ p3) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_47660599739973066508272509402 : (((((False → ((True ∨ ((p3 ∧ (((p4 ∧ p4) → p2) → p1)) → p5)) ∨ p5)) → (((p5 → p5) ∨ p1) ∨ True)) ∧ p5) → (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55794851647677142770788707104 : ((((p3 ∨ p1) ∨ (p5 → True)) ∧ (((p5 ∨ True) → (p1 ∨ (p4 → (p5 ∧ (True ∧ p3))))) ∨ ((((False ∨ True) ∨ False) ∨ p1) ∨ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158371933646447878297861978869 : (((p4 ∨ p3) ∧ (((((False → (p3 → (p1 → (p3 → p1)))) ∧ p5) → (False → True)) → p3) ∨ False)) ∨ (((p4 ∧ p1) ∨ p4) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249335851109955923994851329216 : ((p4 ∨ p5) ∨ (p3 ∨ (((False ∧ ((p4 → (p5 ∧ (p1 ∧ True))) ∧ p3)) ∧ (p4 ∨ False)) ∨ (p4 → ((p5 → p4) ∧ (False → (p5 → False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711037625060578921019078653972 : (((((False → p4) → (p5 ∨ (p5 → True))) ∧ (p4 → ((p4 → ((p1 ∨ (p4 ∧ (p3 ∧ ((p1 ∨ p5) ∧ (p1 → p4))))) → False)) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64845074119733422602562064877 : ((p2 ∨ ((p5 ∨ ((((p4 → p4) → (((False ∨ False) ∨ p2) ∨ ((p3 ∧ p4) ∧ p3))) ∨ (p3 ∧ (p3 → (p4 ∨ False)))) → False)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664628907819619318519618066735 : ((((True → (((p1 ∧ (p3 → ((p1 → p4) ∨ False))) ∧ ((p5 ∨ p1) ∨ p5)) ∧ (True → ((p5 ∧ p4) ∨ (p4 ∨ p1))))) → (p4 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339601561596297116355565872951 : (p1 → (p2 ∨ (((((p4 ∧ ((False ∨ True) ∧ (((p5 ∨ (((True ∧ p1) → p5) → p4)) ∧ p2) ∧ (False ∨ p2)))) ∨ True) ∧ True) ∨ p5) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_48072105480826406095035728914 : ((((((p2 ∨ p5) ∧ True) ∧ (p3 → False)) ∧ (((p4 ∨ p5) → p5) → (p4 ∨ (True → ((True → p2) ∧ (True ∨ False)))))) → (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748109487117585232914498959098 : ((((p1 → p3) → (((p3 → p5) → (((True ∧ p4) ∨ (((((True → p2) ∨ (p2 → True)) → (p4 → p1)) ∨ True) ∨ p4)) ∨ p4)) ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751377946703562955771508088085 : (((True ∧ ((p1 → False) ∨ (True ∧ (((p1 ∨ (((p5 ∨ ((True ∨ p2) ∧ p1)) ∧ True) → p2)) ∧ (p1 → p4)) ∨ ((p3 → False) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341725935860938363199469418826 : (p2 → (((((p4 ∨ p1) ∨ True) ∧ p2) → ((p5 ∧ ((True → (True ∨ p3)) ∧ (((p2 ∨ (p3 → p4)) ∧ p4) ∨ p1))) → p1)) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134504237681823148196975256777 : (((((p4 → (p3 ∨ (p2 ∨ p1))) ∨ (p3 → (((p1 ∨ True) ∨ ((p4 ∧ True) → p4)) ∨ (p1 ∧ p5)))) ∨ p4) → False) ∨ (True ∨ (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52322962007120677279944979736 : (((((p3 ∧ True) ∧ (((p1 ∧ ((p4 ∧ p1) ∨ False)) ∨ p2) → True)) ∨ p3) ∧ ((p3 → (False → p5)) → (p5 ∧ ((False ∨ p3) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245483073000270884271986462950 : ((p2 ∧ p5) ∨ (((p5 → ((((p2 → (True ∧ True)) ∧ p1) ∧ (False ∧ True)) ∨ (p4 → True))) ∨ p3) ∧ (p1 ∨ (p4 → ((p4 ∨ p4) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230497463272864051158840034112 : (((True → p1) ∧ p5) → ((((((False ∧ (False ∨ (p2 → p4))) ∧ ((p2 ∨ p5) → (p3 ∨ p1))) ∧ False) ∧ ((p1 ∧ False) → p5)) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54034336876298658662543771477 : ((((p3 ∨ (p2 → (p5 ∨ (p1 ∨ p2)))) ∨ (p4 ∧ p1)) → (((p5 ∨ (p1 ∧ p4)) ∨ (p2 → ((False → False) ∨ p5))) ∨ (p2 ∨ False))) ∨ p4) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42066787978064784296801886156 : ((((p5 ∨ p3) ∨ (p1 ∧ (True ∧ ((((p4 → p2) ∨ p1) ∧ ((True ∨ (p4 ∧ (((p2 ∨ p1) → p4) ∨ True))) → p3)) ∨ p4)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249108745287306125286171844918 : ((p4 ∨ p2) ∨ (((((p1 ∨ True) ∨ True) → (p1 ∧ ((False ∧ p4) ∧ ((p4 ∨ False) ∧ p4)))) ∨ (True ∨ (False → ((False ∧ True) → p2)))) ∨ p4)) := by
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
theorem thm_5_vars_679974869684413459293390817991 : ((((((((p3 ∧ False) ∨ (False ∨ p5)) → (p2 ∨ p3)) ∨ (((p2 → True) → p3) → (p4 ∧ False))) → True) → (p4 ∨ ((True → p3) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157790276912415750804516671494 : ((((True ∨ (p1 ∧ p3)) → (((p3 → p4) ∨ False) → (p4 ∧ p1))) ∨ (p2 → ((False ∨ True) ∨ p5))) ∨ (((p4 ∧ p1) → (p2 ∨ p2)) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356894899863201266231929778393 : (p5 → ((((p1 ∨ p2) ∨ True) → False) → (((((False → True) ∧ ((p5 ∨ (p3 ∧ p3)) ∧ p5)) ∨ ((p5 → p4) → (p1 ∨ p4))) ∨ p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h11 : ((p1 ∨ p2) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h12 := h2 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : ((p1 ∨ p2) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : ((p1 ∨ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : ((p1 ∨ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171914135281446602869450257736 : (((p3 → ((((False ∧ p5) ∧ p5) ∧ (((p2 → p4) → p5) → p2)) → p2)) → p3) ∨ ((p3 → (((p3 → (p5 → True)) → p3) ∨ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50709600771891667300892608884 : ((((p1 → p5) ∧ (False ∨ (p2 ∨ ((p4 ∧ (p5 ∧ False)) ∨ (((p2 → p5) ∨ (False → p5)) → p2))))) → (p2 ∨ ((p4 → p5) ∧ p5))) ∨ p3) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : ((p2 → p5) ∨ (False → p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- False on the left can always be used.
          apply False.elim h15
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h16 := h13 h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165019178524080791862817829984 : ((((p4 ∨ ((p2 → p1) → p2)) ∨ ((p1 ∧ (p3 ∧ False)) ∨ (p1 → (True ∨ p1)))) → p4) ∨ (p4 ∨ (False → (False → ((p2 ∧ False) ∨ p5))))) := by
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
theorem thm_5_vars_111201008868058587092661991962 : (((((p2 ∧ p1) ∧ p5) ∨ ((p5 ∧ (p3 → (p2 ∧ p5))) ∧ (p2 → ((True → (p5 → True)) ∧ (p4 → (p3 → False)))))) ∧ p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197230773094751166024275017885 : ((((((False ∨ p3) ∧ True) ∧ p4) → p1) → p5) ∨ ((p2 ∧ ((((True ∧ p2) ∨ ((p5 ∨ p2) ∧ p1)) ∨ (p4 ∨ p5)) → (p4 → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37537062274979578170425316779 : ((((p3 ∧ ((p4 → p1) ∨ (((p2 → p3) ∧ p4) ∨ (((p5 ∨ ((p2 ∨ False) ∧ True)) ∨ (p4 ∧ (p5 ∨ p1))) → p5)))) ∨ True) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118580938230523100612054627194 : ((p4 ∨ ((p3 ∨ (((p1 ∧ p5) → (((((True → (p4 ∧ True)) ∨ (p3 → (p5 ∧ p5))) ∨ p3) ∨ p4) ∧ p2)) → p5)) ∨ True)) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166011692272783205454476463290 : (((p1 ∨ p5) ∨ (True ∧ (((False ∨ ((p5 ∨ p3) ∨ (False ∧ p4))) ∨ p3) → (p1 ∧ p1)))) ∨ ((p3 → p3) ∨ ((True → (False ∨ p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115260604606584049818006082421 : ((((p2 → p1) ∧ ((False ∧ (True ∧ p1)) → (False → True))) ∨ ((p5 ∧ ((False ∧ (p2 ∨ (False ∧ p5))) ∨ (p5 ∧ False))) ∨ p5)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9727539954484535720121831687 : ((((p4 → p3) ∨ (False ∨ ((p1 ∨ ((p2 ∨ (p5 ∨ p4)) ∧ ((p5 ∨ p4) ∨ (p5 ∧ (p3 ∧ True))))) ∧ (p2 ∨ (p4 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616426717393763677661221302348 : ((((((p4 ∨ (p4 ∨ ((True → (p3 ∧ p2)) → (p4 ∧ p4)))) → p5) → (((((p4 → p1) ∨ True) ∧ (True ∨ p4)) ∧ p3) → p3)) ∨ p3) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55780865024406394651204794802 : ((((p3 → p5) ∧ (p5 ∨ p4)) ∧ ((((True ∧ ((True → (True ∧ (p5 → p3))) ∧ ((p1 → p1) ∧ p4))) → p5) → p2) ∨ (False → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308626062015955687033231970537 : (p2 ∨ (((p4 ∧ p2) → (((p4 ∧ ((p5 ∨ ((p1 ∨ p3) ∧ ((False → p4) ∧ False))) ∨ p4)) ∨ ((p2 ∨ p1) → (p5 ∨ p2))) ∧ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300674044714254192479341845050 : (False ∨ ((((p5 ∧ p5) ∧ ((((p3 ∨ (p3 ∨ p2)) → False) ∨ (True → p3)) → p2)) ∨ (False ∧ p3)) ∨ ((p1 → (p4 → (True ∨ True))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232161421266881923736571321590 : (((True → p3) → p4) → (((False → p2) → (p3 ∧ ((True ∨ p5) ∨ (p5 → p2)))) ∨ (False → ((p4 ∨ (False ∨ (p4 ∨ (p2 ∧ True)))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114011781554759286556348012556 : ((((p4 ∨ ((False → ((p1 → ((p4 ∨ p1) ∧ (p3 ∧ (p3 → p1)))) → p3)) → (False ∨ p1))) ∧ False) ∨ ((p5 ∨ p4) ∨ True)) ∨ (p3 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319457830190983126044998528995 : (p4 ∨ (((((p1 → False) ∨ p5) ∧ (True ∨ p1)) ∨ ((p2 → p1) ∨ p4)) ∨ (p5 → (((p5 ∨ p3) ∧ (p5 ∧ ((p4 ∨ p2) → p5))) → p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354578377888417708360872371673 : (p5 → ((((p3 ∧ (p2 ∧ (((p1 → False) ∨ False) → p1))) ∨ (False ∨ (p2 ∧ (((p2 → p3) ∧ (True ∧ (p5 ∨ p3))) ∨ True)))) ∧ p5) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158691812314634814097612845452 : ((p2 ∧ ((False ∨ p4) → ((((True → True) → p4) → (p2 ∨ True)) ∧ ((p4 ∨ p5) → (p5 ∨ p1))))) ∨ ((True → (p1 ∨ True)) ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37843431462495147896811959345 : ((((p5 ∨ ((p3 ∨ ((p1 → ((p3 ∨ (p2 ∨ p1)) ∨ p3)) ∧ ((p1 ∧ ((p4 ∨ p5) ∧ True)) ∨ (p5 → p1)))) ∧ True)) → p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227087453816156014556413579314 : (((p3 ∨ p4) → p2) ∨ (((p2 ∨ (True ∧ (((p3 ∨ True) → False) ∧ ((True ∧ ((p5 ∨ (p5 → (p2 ∧ p1))) ∧ p4)) ∨ p1)))) → p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h14 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h15 := h6 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h17 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h18 := h6 h17
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h20 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h21 := h6 h20
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8321725360422351895268980652 : (((((False ∧ (p1 ∨ ((((p3 ∨ p2) ∨ p5) → (((p5 ∧ p2) → True) ∨ p2)) ∨ (p1 → False)))) → ((p4 → p4) → True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62701588660646074468890359785 : ((p4 ∧ ((((((p2 ∨ p3) ∨ False) ∧ ((True → (p4 ∧ True)) → False)) → (p2 ∨ p4)) ∧ ((p3 → (p4 ∧ (p4 → p2))) ∧ p5)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43369834668311201761279838472 : ((((((p5 → p2) → ((((p1 ∨ True) ∧ p4) ∨ True) ∧ (True → (p5 → ((p3 ∨ p5) → (p1 ∧ p3)))))) → (p5 → p4)) ∨ p3) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21456295167742877133755854063 : ((((p2 → (p2 ∨ (p3 ∨ (True ∧ p4)))) ∧ (False ∨ p3)) ∨ ((p3 → (p4 → True)) ∧ ((((p1 ∨ (False ∨ p1)) → p5) → p1) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317941048855130278547694790520 : (p4 ∨ ((p2 ∨ (p4 ∧ (True → ((False ∨ (p3 → (False ∨ p2))) ∨ (((p3 ∨ ((True ∨ p2) → p5)) → p4) → ((p5 ∧ p3) ∧ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696260150048097799299360741607 : ((((True → ((p2 ∨ (p4 ∨ (p2 ∧ (p5 ∨ (False ∨ False))))) ∨ (p2 ∨ p4))) → (p5 ∧ ((p4 ∨ (False ∧ ((p2 → p1) → p4))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_523405172301018318915492651875 : (((True ∧ ((((p5 ∨ (p3 ∨ ((p4 → ((((((p5 ∨ p1) ∨ p1) ∨ p2) ∨ p5) → p3) ∧ p1)) ∨ True))) ∨ (p3 ∨ p1)) → p2) → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ (p3 ∨ ((p4 → ((((((p5 ∨ p1) ∨ p1) ∨ p2) ∨ p5) → p3) ∧ p1)) ∨ True))) ∨ (p3 ∨ p1)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329672445821827506518481684477 : (True → ((False ∨ p3) → ((((p2 → (p1 ∨ True)) → False) ∧ (((((p2 → p2) ∧ p1) ∨ (p2 → p3)) ∨ True) ∧ p3)) → ((True → p2) ∨ True)))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625837515910674503164235857812 : ((((p1 → (p4 → ((True ∨ ((True ∧ (((p2 ∨ True) ∨ p3) ∧ p1)) ∨ ((True ∧ (p5 ∨ p1)) → p5))) → ((p5 → p3) → p2)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164507708625961962715593856073 : ((((((p5 ∧ ((p4 → False) → False)) ∨ (p1 ∨ (False ∧ p4))) ∧ p2) ∧ (True → p4)) ∧ False) ∨ ((p3 ∧ True) → (((p1 ∨ False) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_188704671176487995136403194696 : ((((p1 → ((p3 → p4) ∧ True)) ∧ False) → (True ∨ p3)) ∧ (p2 → ((((True ∨ p4) ∨ (p1 ∧ True)) → ((p1 ∧ (p1 → p5)) ∨ p3)) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165031769369191214896117474011 : (((((p2 → False) ∧ p4) → (p5 ∧ (p5 ∨ (p1 ∧ ((p1 ∧ (p1 → False)) ∨ False))))) → p1) ∨ ((p1 ∧ ((p5 → p2) ∧ (p2 ∧ p3))) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178190714421098571103074634457 : (((p3 ∧ (p1 → (p1 ∧ (((p2 → p2) → p5) → (p3 ∨ p1))))) → False) ∨ (((p3 ∨ (p3 → True)) ∨ (False ∨ (False ∨ p5))) → (True ∨ True))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112543547234914309369503305178 : ((((((((p1 → p4) ∧ True) ∨ p4) ∨ (p2 ∧ True)) → ((p2 ∨ (False ∧ p2)) ∧ (((p2 → p5) ∨ p3) ∧ False))) → p4) → False) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68303165184864430553574447165 : ((p3 → (((p4 ∨ ((True ∧ ((p1 ∧ p5) ∨ (p3 → (p4 ∨ (p3 ∨ p2))))) ∨ p1)) ∧ (p3 ∧ p2)) ∧ ((p1 → (False → p1)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191583434735053165580944421926 : ((p2 ∧ ((p3 ∨ p2) ∨ ((p5 ∧ (True → p3)) ∨ p5))) ∨ (((p2 ∧ ((p1 ∧ (p1 ∨ False)) → False)) ∧ ((True ∧ False) ∧ (False ∧ p3))) → False)) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116140054205909026800552287769 : (((p4 ∧ (p2 → False)) ∧ ((False ∨ ((p5 → p2) ∨ (p3 ∧ p2))) ∨ (p4 ∨ (True ∧ ((p4 ∨ False) → (p5 ∨ (p3 ∧ p3))))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602914835078171064586350449544 : ((((p1 ∨ (((p5 ∨ True) → (p2 → (p4 ∧ ((((p2 ∨ False) → p3) → ((p3 → False) ∧ p4)) ∨ False)))) ∨ ((p5 ∧ False) ∨ False))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50840524547496598751102019649 : (((((p3 → False) → (((p4 ∧ (p5 → True)) ∧ False) ∧ ((p3 ∨ (p2 → False)) ∨ p4))) ∧ p1) ∧ ((p2 ∧ (p5 ∨ (True ∧ p5))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725687376782971095423735876575 : (((((True ∨ p5) ∧ False) ∨ (p1 → (((p4 ∧ (p2 ∧ (p5 → (((p4 ∨ (p4 → True)) ∨ p3) → ((True → False) → p1))))) ∧ False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_518831471475049488368827783716 : ((((p5 ∧ p3) → ((False ∨ (p4 ∨ ((p4 → (p3 ∧ (p4 ∨ ((p1 ∨ (True → True)) ∧ p2)))) → (p4 → (p2 ∧ True))))) ∨ (False ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_115910052534169764768870605860 : ((((p2 ∨ False) ∧ (p1 → False)) ∨ (((((((False → p3) ∨ True) ∧ p1) ∨ (p5 → p2)) ∨ p4) → p5) ∨ (p2 → (True ∨ p2)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241355734628004120352067076223 : ((False → False) ∧ ((p1 ∨ ((p4 ∧ (p3 → p2)) → ((((p1 ∨ p2) ∨ False) → True) → p3))) ∨ ((False ∧ ((p2 ∧ p4) → p5)) → (p4 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
theorem thm_5_vars_150253061132477283429665320081 : ((p3 → (((((p5 → p3) → (p1 ∨ p4)) ∨ (p5 ∧ (p5 → p1))) ∧ p3) → (p5 ∨ (p4 ∧ (p1 ∨ p2))))) ∨ ((True ∧ False) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708933453674844510173454988707 : (((((p1 ∨ ((p4 ∧ True) ∨ p2)) ∨ (True ∨ True)) → ((p1 ∧ (((((True → False) ∨ False) ∧ True) → p2) → ((p3 ∧ True) ∧ False))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137235159701243885650899561321 : ((p1 ∧ ((p4 ∨ (((False ∧ p2) → ((p5 ∧ (p5 ∧ ((p3 ∧ (False ∧ False)) ∧ p4))) ∨ False)) → p2)) ∨ (p2 ∧ p1))) ∨ (p5 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53890423170006838681512189708 : (((False ∧ ((p5 ∧ (((p3 ∧ p3) ∨ p3) ∧ p2)) ∧ p4)) ∨ ((((True ∨ p1) ∧ p2) → True) ∨ (((True ∨ (p4 ∨ p3)) ∧ p2) ∧ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585776403197156645496701187208 : ((((((True ∧ (p2 → (((((False ∨ True) ∧ (p1 ∨ (p4 → p1))) ∧ (p3 ∨ (p3 ∧ (p1 ∨ True)))) ∧ p1) → False))) → p4) ∧ p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698683860880504608123427164990 : (((((p4 → (p4 ∨ True)) → (p5 → (((p2 ∧ p4) ∧ p3) → False))) ∨ (p1 ∨ (p1 ∧ (((p5 → (True ∧ False)) → (p4 ∨ p1)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606320732590553582596960222411 : ((((((((p5 ∨ (((p1 → False) ∨ (False ∨ p2)) ∨ p3)) ∨ ((p4 ∧ ((p2 → p3) ∧ (True → p2))) ∧ False)) ∨ p1) ∨ False) ∧ p5) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51933851540609199509633736797 : ((((p1 → (((p1 → p1) ∨ p1) ∧ ((True → p2) ∨ True))) → ((True ∨ p2) ∧ p1)) ∨ (((True → ((p3 → False) → p3)) → True) ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932975934088179869844672884917 : ((((p2 ∨ (p2 → (((p5 ∧ True) → p1) ∧ p4))) ∧ ((True ∨ p1) → ((p3 ∨ p4) ∧ (((((p2 → p3) ∨ False) ∧ p4) ∧ False) ∧ p2)))) → p1) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133803653916998125221359040611 : ((((False → (p1 ∧ p1)) → ((((p4 ∨ True) ∨ (False ∨ (False → (p4 → False)))) ∧ False) ∧ (False ∧ (False ∧ p4)))) ∧ True) ∨ (True ∨ (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42946735138024965844572790724 : (((p4 → ((True → p3) → (p1 ∧ ((((p2 → (((False → p3) → p1) ∧ p4)) → True) ∧ (p2 ∨ True)) → ((False ∨ False) ∧ p1))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219756937781868869553812904367 : ((p2 → ((p4 → p4) ∧ p2)) → ((p4 ∧ ((p5 → (False ∧ (p4 ∨ p3))) → False)) ∨ ((p5 → False) ∨ (p4 → ((p5 → (p5 ∧ True)) ∨ p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80804821715686097581526717052 : (((p5 → (((((p1 → (p4 ∨ p5)) → ((p1 ∧ p5) → p3)) ∧ p3) → (False ∧ (p1 ∨ ((p5 → False) → p1)))) ∨ True)) → (p3 ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((((p1 → (p4 ∨ p5)) → ((p1 ∧ p5) → p3)) ∧ p3) → (False ∧ (p1 ∨ ((p5 → False) → p1)))) ∨ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178416476842770928544025399970 : (((False ∨ (p5 → ((p1 ∧ p3) ∨ ((p1 ∨ p2) ∨ p4)))) → (p2 → p4)) ∨ ((False → ((p3 ∨ ((p3 → (p2 ∨ p5)) ∨ p3)) ∨ p4)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147947877656078275171999816031 : ((((p1 → p5) → ((p5 ∨ p4) ∧ ((True ∧ (p2 ∨ True)) → (((p1 ∨ p5) ∨ True) ∨ True)))) ∧ (p1 ∨ p3)) ∨ ((True → (p5 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8136475964442447307172108454 : ((((True ∧ ((p5 ∨ (p4 ∧ p4)) ∧ (p5 ∨ (False ∧ (((p2 ∧ False) ∧ ((p1 ∧ p3) ∧ (p5 → p2))) ∨ (True ∨ p3)))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669825389918035088519423093438 : ((((((p2 → (p1 ∧ ((False ∨ (True → p2)) ∨ p4))) ∧ (p3 → p4)) ∧ ((p2 ∧ p4) ∧ (p4 → (False → True)))) ∨ (p4 ∨ (True ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760652781361701354422955354276 : (((p2 ∧ (p5 ∧ ((((p1 ∧ (p1 ∧ (True ∧ (p5 ∨ (p1 → ((p5 ∨ p2) ∨ p3)))))) → True) ∧ True) → (p1 ∨ (True ∧ (p2 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50334814019470647850309069666 : ((((((True ∧ p4) → ((p3 ∧ p2) ∧ p4)) → False) → (True ∧ (((p1 → p4) ∧ (p2 ∨ p2)) → p2))) ∨ ((p4 ∧ (p2 ∧ p2)) → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504792881179142315612919690071 : ((((p4 ∨ (True → True)) → ((((False ∧ p3) ∧ p4) ∨ (True ∨ (p5 ∨ p3))) ∨ ((p5 ∨ False) ∧ (p3 → (((p2 → p5) ∨ p5) ∧ p1))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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



