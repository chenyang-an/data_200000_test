variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217036546818945713841946696096 : ((((p1 ∨ p1) ∧ p1) ∨ p2) → (((((p4 ∨ (p4 ∨ p2)) → ((p4 ∨ (p3 → p2)) ∨ True)) ∧ p1) ∨ False) ∨ (((True ∨ p3) ∨ p2) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44359433238420170927381176964 : (((((p4 ∧ (p1 ∨ (((p3 ∨ (p5 → (p1 → p4))) → p1) → p1))) ∨ p5) ∧ ((p3 ∨ False) → ((p5 ∨ (p2 ∨ p5)) ∧ False))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171594704877850970260291976263 : ((((((p1 → p4) ∧ (False → p2)) → (p1 ∧ p5)) → (p5 → (p4 ∨ p1))) ∨ p3) ∨ ((((p4 → ((False ∨ p3) ∨ p5)) → p2) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47069907744714801114684848164 : ((((p3 ∧ ((((p5 → True) → (p1 ∨ ((p2 ∨ p3) ∧ p2))) → (p5 ∧ p1)) ∧ (p3 → (p2 ∧ True)))) ∨ (True ∨ False)) ∨ (p1 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178809346240778012052153532014 : (((True ∧ (p2 ∨ p5)) ∨ ((p5 ∧ (True ∧ ((p2 → p5) → p2))) ∨ True)) ∨ (((p3 ∨ True) ∧ ((False → (False ∧ (True ∧ p4))) → p2)) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216054118685948008825298895795 : ((p5 ∨ (p5 ∧ (p2 → True))) ∨ (((p3 ∨ ((p2 → ((False ∨ p3) ∨ (p1 ∨ p3))) ∨ p1)) → False) ∨ (True ∨ (((p5 → False) → p1) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244636413387372966978223243535 : ((False ∧ p5) ∨ ((p2 ∧ (((p2 ∨ (p3 ∨ p3)) ∨ True) ∨ (p3 → (p4 ∨ p5)))) ∨ (((p1 ∧ (False ∨ ((p3 ∨ p2) ∧ p4))) ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191636929555599041043102673679 : ((p4 ∧ (((False ∧ (p1 ∨ (p2 ∨ p1))) → False) → p3)) ∨ (((p4 ∧ ((p2 ∧ p2) ∧ (p1 ∧ (p2 ∧ p2)))) → p1) ∨ ((p2 ∧ p4) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h8 := h5.left
  let h9 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112182284819464842017551050463 : (((p4 ∧ (p3 ∨ ((((p2 ∨ (True → ((True ∧ (p1 → p2)) ∨ p4))) → p5) ∨ ((p4 ∧ False) ∨ False)) ∧ (p5 → p4)))) ∨ p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678569296604624950957942738725 : ((((((p4 ∨ p2) → p4) → ((p4 → False) → (p4 ∧ (p2 → (p5 ∧ ((p3 → False) → (True → p5))))))) ∨ (((True ∨ False) → p3) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168147391317835269765586773178 : (((p5 → (p3 ∧ (p3 → p1))) → ((p5 ∧ ((True → (p3 → p4)) ∨ (p3 ∨ False))) ∧ False)) → ((p3 → False) ∨ ((p3 → False) ∨ (False → True)))) := by
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
theorem thm_5_vars_52626448975171487311506824514 : ((((False → (True ∨ p2)) → ((((False ∨ True) ∨ p1) ∨ (p5 → False)) → p4)) ∨ (((((p2 → p4) ∨ p2) ∧ True) ∧ (p4 ∧ p5)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317769110442230411854701586761 : (p4 ∨ ((((False → (p1 ∨ p4)) ∧ ((((p5 ∨ (p3 → p5)) ∨ p2) → False) → p2)) ∧ ((p1 ∧ ((False ∧ p3) ∨ (p2 ∧ p3))) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111768661252056633666775517317 : (((((p5 ∨ p5) ∨ ((((p5 ∧ (p3 ∨ p2)) → ((True ∧ (p1 ∨ p4)) ∨ (False ∧ p4))) ∧ p3) ∨ False)) ∧ (p5 ∨ p5)) ∨ p4) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717703300620281853117735137706 : ((((((False → p3) ∧ p2) ∧ p2) ∨ (p5 → (((((True → ((p1 ∧ p3) ∧ p4)) → (p3 ∧ (p2 → (p2 → False)))) → True) → p3) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45044878788414263839474875586 : ((((True → p1) ∨ (((p5 ∨ (p3 ∨ ((((p2 ∧ (((True ∨ (p4 → p5)) ∨ p1) → True)) ∧ p2) ∨ p5) → p3))) ∨ p3) → p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_557393390403747365828102353191 : (((p3 ∨ ((p5 ∨ (p3 ∧ True)) ∨ (p4 ∨ (((((((p3 ∨ ((p4 ∧ p3) → p3)) ∧ True) → True) → (p2 → p1)) ∧ True) ∨ True) ∨ p3)))) ∧ True) ∧ True) := by
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
theorem thm_5_vars_42596302285992378557327462077 : (((p2 ∨ (p5 ∧ ((p5 → p3) ∨ ((p3 → ((p4 ∧ p4) ∨ p1)) ∧ (((p2 ∨ False) ∨ ((p4 → p2) ∨ (p5 → p5))) ∨ p5))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184787664194626417931912498698 : ((((p5 → (p2 ∧ p5)) → p5) ∨ ((p2 ∧ (True ∨ True)) ∧ p3)) ∨ ((((p1 → p4) ∧ (True → (p4 → (p3 → (True ∨ p4))))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180046417760438247113930522093 : (((p1 ∨ (((p1 ∨ p3) → (p2 ∨ (p5 ∧ (True ∧ p4)))) ∨ p4)) ∨ True) → ((p1 ∨ ((True → (True → ((False ∧ True) → p2))) ∧ p2)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230487613699587153408915367988 : (((True → False) ∧ True) → (p1 ∨ ((True ∧ ((p4 ∨ (p2 ∨ (((p4 ∧ p1) ∨ (p2 → (p1 ∧ p4))) → True))) ∧ (False ∨ p4))) ∧ (False → False)))) := by
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
theorem thm_5_vars_711699762660224918619360888483 : ((((p5 → ((p3 ∨ p1) → (p4 ∨ p3))) ∧ ((False ∨ p2) ∧ (((True ∧ (((p2 → p4) ∧ (p4 → False)) → (p2 ∨ p4))) ∧ p2) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606646284850834665237517574270 : ((((((p2 → (((p5 ∨ (False → ((p3 ∧ ((False ∧ p1) ∨ (True → True))) ∨ p3))) ∧ (True → p1)) ∧ (False ∧ False))) → p3) ∧ p3) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_652973296563506537787900538359 : ((((p5 ∨ (((((p5 ∨ False) ∨ (((p2 ∨ p3) → p3) ∧ p1)) → p4) ∨ (p2 ∨ (p5 ∨ p5))) ∧ ((p3 → p5) ∧ p3))) ∧ (False → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313818802463114934497685789546 : (p3 ∨ ((((p5 → p4) ∧ ((False ∨ ((((True ∨ p1) ∧ ((p1 → (True ∨ (p5 ∧ p4))) ∨ p1)) ∨ p5) ∧ p3)) ∧ p3)) ∨ True) ∧ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149406529400069066863035876318 : ((True ∧ ((((((((p3 → (p5 ∨ p4)) ∨ False) ∧ p2) ∨ p5) ∨ True) ∧ p2) → (p3 ∨ False)) ∨ (p2 → p2))) ∨ (p4 ∧ (True ∧ (p5 → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695876378348962705669557249635 : (((((p2 ∧ p5) ∨ ((p4 ∨ ((p5 ∧ p5) ∧ p4)) → (p3 ∨ (False ∨ p1)))) → (p5 ∨ (((False → (p3 ∨ (p1 ∨ p3))) → p2) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148548133512536650769435289366 : (((((p4 ∨ ((p5 ∧ p1) ∨ (p3 ∧ p3))) ∨ p4) ∨ p2) ∧ (((p3 ∧ (p5 ∨ p5)) ∨ (p1 ∧ p1)) → False)) ∨ ((p2 ∧ (p5 ∨ False)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228826424166609071966989860055 : ((p3 ∨ (p5 ∨ p3)) ∨ (p5 ∨ ((p1 ∨ ((p3 → True) ∧ (p3 ∨ (p1 ∨ ((True ∨ p1) → (True ∨ (((p2 ∧ p1) ∧ p2) → p3))))))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51771071801242431266933065405 : (((True ∧ (p1 → (((p3 → p4) → ((False ∨ True) ∧ True)) → (p3 ∨ (p2 → p1))))) ∧ (p2 ∧ (((p4 → False) ∨ p1) ∧ (False ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147416861074888658013699148079 : (((((p5 ∨ False) → (p4 → False)) → ((p2 → (((p2 ∨ False) → (False ∨ p1)) ∧ (True ∨ p3))) ∨ p2)) ∨ True) ∨ (p1 → (p5 ∧ (p2 → p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252285518897060481410166749330 : ((p4 → p5) ∨ (((p2 ∨ (p2 ∨ False)) ∨ (p2 ∨ (False ∧ (True ∨ (False ∨ ((p1 ∨ p5) ∨ p4)))))) ∨ ((p4 ∧ p1) → (p5 ∨ (p2 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762437193501809393531916672923 : (((p3 ∧ (((False → p3) → ((p4 ∧ True) → (False ∧ ((True → (((p4 → p2) ∨ p4) ∨ p3)) ∨ True)))) ∧ (p3 ∨ ((p2 → p4) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684295000731396541469152380749 : (((((p2 ∧ (((p3 ∧ False) ∧ (p2 ∨ p5)) ∨ ((p4 → p5) ∨ True))) ∨ (p2 ∨ (True → True))) ∨ (((p2 ∧ p5) → (p4 ∨ p1)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_57365842438816246221533032616 : (((p4 ∧ (p1 ∨ p1)) ∨ (((p4 → p5) ∨ (((p4 ∧ ((False → p1) → (p2 → True))) → (p1 ∨ (p3 → (p1 ∨ True)))) ∨ p3)) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605470198052614760913717219634 : ((((p3 → ((True → p2) ∧ (((((((p4 → p3) ∧ (p5 ∧ (p5 ∧ True))) ∨ p4) ∧ (p1 ∧ p2)) ∨ (p1 → p4)) ∨ p1) ∨ p5))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354848547645854138319887386523 : (p5 → (((p3 ∨ False) ∨ ((p5 ∧ ((p2 → (p1 ∧ (p2 → p4))) → p1)) ∨ (((p1 ∧ False) ∨ (p5 ∧ p3)) ∨ (True → (p3 ∧ p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336449877688261598472563324644 : (p1 → ((p5 ∨ (p1 ∧ (p2 ∨ (((p4 → (p1 ∧ p3)) ∨ ((p4 → (((p2 ∧ p2) ∨ p2) ∨ p2)) ∧ (p1 → (p2 ∧ p3)))) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631704495742544613793358728256 : (((((((p3 ∧ (False ∧ ((False → p5) ∨ p1))) ∧ (p1 ∨ (p2 ∨ False))) ∧ ((p4 ∧ ((False ∨ p5) ∨ (p1 ∨ p3))) ∨ p4)) → p2) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175954502522609481565702538289 : (((p2 ∨ (((False ∨ True) → (p3 ∨ (p2 ∧ p5))) ∨ (p2 ∨ p4))) ∨ True) ∧ (p5 → (p5 ∧ (True ∨ (p1 ∧ (p4 ∨ (p4 → (p4 ∧ p5)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63076536500125779746321923248 : ((p5 ∧ (((p3 ∧ ((p5 ∨ True) ∧ (((p5 ∧ p5) ∨ (((p4 → False) ∨ (True ∨ (p5 → p2))) ∧ p1)) ∨ (p2 ∨ p4)))) ∨ p1) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717066337927382174159860105919 : ((((True ∨ ((p4 ∨ True) ∨ True)) ∧ ((((((((p3 → False) → p1) ∧ p5) ∨ (p1 ∧ True)) → p3) → (p2 ∧ (p4 ∨ p2))) ∨ False) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177844579310736586006946236825 : ((((p1 ∧ (p1 ∨ (((p1 → (True ∧ p3)) ∨ True) → p5))) ∧ False) ∨ p4) ∨ (p5 → (p3 ∨ ((False → p1) ∧ (p5 ∧ (p2 → (p2 ∧ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48595269764354315752023128267 : ((((False → (((True ∨ ((p2 ∧ p3) ∧ True)) ∧ (True ∨ (((False ∧ True) ∨ p5) → False))) → p3)) ∧ (p5 ∧ p5)) ∧ (False ∨ (False ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227568936577061839778007062485 : ((False ∧ (True ∧ True)) ∨ ((((p1 → p1) → ((p2 → p3) ∧ (p4 → p1))) ∨ p4) ∨ ((p5 → (p1 ∨ True)) ∨ (((False ∧ p1) ∧ p5) ∨ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61223417209644201101220374247 : ((False ∧ (p1 ∧ ((((((True ∨ (p1 → p1)) → p3) → (p3 ∧ ((p4 ∧ p1) ∨ ((p3 ∧ p5) → (p1 ∧ p4))))) ∧ p5) ∨ p3) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96259853249018938584007194508 : ((False ∨ ((((p1 ∧ (p1 → ((p5 ∨ (False → (p5 ∧ p5))) ∧ p5))) ∧ (p3 → True)) ∨ (((False → p3) ∧ (True ∧ p2)) ∧ False)) ∧ p4)) → p5) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157502916969720835334884269573 : ((((p1 → p5) ∨ ((((p4 ∧ False) ∨ p3) → (p2 → p1)) → ((p1 ∧ p5) → p2))) ∨ (p3 ∧ p3)) ∨ ((p5 ∨ p5) ∨ (True ∨ (p5 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354830285643349646967300726962 : (p5 → (((p3 ∨ (p3 → p1)) → ((True ∧ ((p5 ∨ p2) → ((p5 ∧ ((True ∧ p2) ∨ (p5 ∨ ((p4 ∨ p1) ∧ p4)))) ∧ p4))) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730799822046974078855073427383 : ((((p4 ∧ (p3 → p5)) → ((p1 → (((True ∧ (p4 ∨ p2)) ∨ (p4 ∧ p4)) ∧ ((p2 → (p5 ∨ p2)) ∧ ((p5 ∧ True) ∨ p5)))) ∨ p4)) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315366432698157404729053446157 : (p3 ∨ ((False ∨ (True ∨ False)) ∧ ((((((p5 ∧ False) ∨ False) ∨ False) → False) ∨ True) ∧ ((((p5 → (p5 → False)) ∨ p3) ∨ p1) ∨ (p4 → p4))))) := by
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
theorem thm_5_vars_259024784237180697756809838879 : ((True → p4) → (((p2 ∨ (p5 ∨ (True → p1))) → ((p3 ∧ False) ∨ (True ∨ (p5 ∨ (False ∧ (p5 ∧ p5)))))) ∨ ((False ∨ (p3 → False)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308579550560133804435188634017 : (p2 ∨ ((((p1 ∧ (True → p2)) → p4) → ((((False ∨ p3) → (p2 → p2)) → (p2 ∧ (p4 → ((p4 ∧ True) ∨ (p1 ∨ p2))))) ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_171776975680090598123765617162 : ((((((((True ∨ p5) ∨ p3) ∧ p3) ∨ (True → True)) → False) ∧ (p4 → p5)) → p5) ∨ (p4 ∨ ((p1 → (p3 ∨ (p2 → (True ∧ p1)))) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∨ p5) ∨ p3) ∧ p3) ∨ (True → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123697264565078799679996733667 : (((((((p3 ∧ ((p4 ∨ p1) → False)) ∧ (p3 ∨ p3)) ∧ True) ∧ p2) ∧ p4) ∧ (p2 ∨ ((True ∨ (p5 → (p3 → p2))) → p3))) → (False ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h15 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h16 : (p4 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h17 := h13 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h19 : (p4 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h20 := h13 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h23 : (p4 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h24 := h13 h23
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h26 : (p4 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h27 := h13 h26
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57113489223999489639631626195 : ((((p2 ∨ p3) ∧ p2) ∨ ((((((p5 ∧ p2) → p1) ∨ True) ∨ p4) → ((p4 ∨ (p3 → (p4 → p3))) ∨ (p1 ∧ p5))) ∨ (False ∧ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261545240641920560862243407363 : ((p5 → p3) → (True → (p2 ∨ (False ∨ (((p1 → p2) ∧ p2) → ((((p4 ∨ p1) ∧ False) ∨ (False → True)) ∨ (p1 → ((p4 → p3) ∧ p4)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338393784344474913096949581082 : (p1 → (((p4 ∨ (p5 → False)) ∧ True) → (((p2 ∧ (True → (((p3 ∧ ((p1 → (p1 ∧ p4)) → p1)) ∨ p2) → p2))) ∨ False) ∨ (p2 ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63391182810031807282410607945 : ((p5 ∧ (p1 ∨ ((p4 ∨ ((p1 ∨ False) → ((p5 ∧ p2) ∨ p5))) ∧ (p3 → ((p3 ∨ ((p3 → p3) ∧ (p2 ∧ (False ∧ p3)))) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253127794279728709820548596446 : ((True ∧ p5) → ((((False ∨ ((p5 ∨ False) ∨ (p1 ∧ ((p5 → p1) ∨ True)))) → (p2 ∧ (p3 → False))) ∨ ((p4 ∨ True) ∨ True)) ∨ (p1 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798294088421508453685241796899 : (((p1 → ((((((p3 → p5) ∨ (p3 ∨ True)) → (False ∨ (p3 → True))) → False) ∧ p1) ∧ (p4 ∧ (False → ((p4 ∨ (True ∧ False)) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600014160450648561599125772467 : (((((False ∨ p4) → (((((((p4 → p2) ∨ (p4 ∨ (p2 ∨ p4))) → p5) ∧ False) ∧ p1) ∨ ((p4 ∧ p4) → p2)) ∧ (p5 → p5))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674989627386638297158166500157 : (((((((p5 → p2) → True) → ((True ∧ (p3 → ((p5 ∧ (p1 ∨ p3)) ∨ (True ∧ False)))) ∧ p1)) ∧ True) ∧ (True ∨ ((False → False) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356865048076728253759199884099 : (p5 → ((p2 ∧ ((p3 → p2) ∧ True)) ∨ (((((p4 → p2) → (p4 → p5)) → (p3 ∨ False)) ∨ (((True ∨ False) ∧ True) → p3)) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_352156131348840665366560289403 : (p4 → ((True ∨ (p1 → (p5 ∧ (False ∧ p4)))) → ((False ∧ ((((False → p4) → False) ∧ p1) ∨ (p3 ∧ (p5 ∨ (p3 ∨ (p2 → p2)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134300511412254408725724152362 : ((((p5 ∨ p2) → (p4 ∧ ((p2 → (p1 ∧ (False ∧ (((((True ∧ p1) ∧ p3) ∨ p2) → p4) ∨ False)))) → p4))) ∨ p2) ∨ ((p2 ∧ True) → p2)) := by
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
theorem thm_5_vars_336187572443508542591434211719 : (p1 → ((((p3 → ((((p4 → p5) → p5) ∨ False) → (p3 ∨ (((p4 ∨ (True ∨ p1)) ∨ False) ∨ True)))) → (p1 → False)) ∧ (p2 ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40495995741894394010169407723 : ((((True ∧ (((False ∧ (((p5 → p3) ∧ ((p5 ∧ p2) ∨ (True → (p5 ∨ (False → (p3 → p2)))))) ∨ True)) ∨ p2) ∨ p2)) ∨ True) ∨ p5) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301842972457703511420802253066 : (False ∨ ((p5 ∨ p1) ∨ (p3 ∨ (p5 ∨ (((False ∧ ((p5 → p4) ∧ (p5 ∧ ((p2 → True) → p5)))) ∨ p5) → (True ∨ (p4 ∨ (p5 ∧ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61650858946420309902992823468 : ((p1 ∧ (p1 ∧ ((False ∨ (p5 → ((p5 ∧ ((p3 ∧ ((p3 → p4) ∨ (p1 ∨ False))) → p4)) → p4))) ∨ (False ∧ ((True → p1) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132870082450911039832300325661 : ((p3 ∨ (((p3 ∨ (p1 ∨ (True → (p4 → p3)))) ∨ (p1 ∨ ((p5 ∨ p5) → (True ∨ (p2 → p1))))) ∨ (False ∧ False))) ∧ (True ∨ (p5 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38301739329892364948345903081 : (((((((p4 ∧ (p2 → False)) ∧ p2) → ((p3 ∨ p1) ∧ ((False ∨ (p3 ∨ p4)) ∧ p5))) ∨ p2) → ((p4 ∨ (False ∨ p4)) ∨ p4)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151899610135048727056625905994 : (((((p3 ∨ p4) → p2) → ((p5 ∧ (p1 ∧ p5)) ∧ ((p1 → False) → p4))) → ((False → (p4 ∧ p3)) ∧ p5)) → (((p4 ∧ p1) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204265501067196704720462728047 : ((((p2 ∨ p5) ∨ (p5 ∧ p4)) ∧ True) ∨ ((p2 → (False ∨ p3)) ∨ ((((True ∧ p4) → True) → (p4 ∨ ((p3 ∧ False) → p3))) ∨ (p1 → False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114039576319016908715842855259 : (((((((True ∧ p2) ∧ ((False ∧ True) → (p1 → False))) → p1) ∧ (p2 ∨ (p5 ∨ p1))) ∧ (p3 → False)) ∨ (p5 ∨ (False → p2))) ∨ (False ∧ True)) := by
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
theorem thm_5_vars_690779037956715524696343987551 : ((((((((p4 ∨ p2) ∧ p1) ∨ ((p3 → False) → False)) → (p5 ∨ (p3 ∨ True))) → p3) → ((p5 → (p2 ∧ p5)) ∨ ((p4 ∨ p2) → p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ p2) ∧ p1) ∨ ((p3 → False) → False)) → (p5 ∨ (p3 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127332359861015531252995563039 : ((p2 ∨ ((True → p1) ∨ (True ∧ (p3 ∨ ((True ∧ p5) ∨ (p2 ∨ (p2 → (((p3 ∧ ((p2 ∨ p2) ∨ p4)) ∧ p4) → p4)))))))) → (False ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330416084493486043415675421305 : (True → (p3 ∨ (((p5 ∧ (((False ∧ (((((p1 ∧ (p4 ∨ p2)) ∧ False) ∨ False) ∨ (p4 ∧ p3)) → p3)) ∨ p1) ∧ (p5 ∨ p2))) ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197040187040281814132582508935 : ((((p3 ∧ p4) ∧ ((p3 → p4) ∧ p4)) ∨ p1) ∨ (p5 → (p3 → (True ∨ (((p3 → p5) ∨ False) ∧ ((p5 ∨ (p1 ∧ (True ∧ p3))) → True)))))) := by
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
theorem thm_5_vars_184776091303955621973768856536 : ((((p4 ∨ (p3 ∨ p1)) ∧ p5) ∨ (p1 ∧ (True ∧ (p2 ∨ p3)))) ∨ ((p1 ∧ True) ∨ (((True ∨ (p1 ∨ ((True ∧ True) → True))) ∨ False) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156822026161180947068444827706 : (((p4 ∨ ((p5 → (p3 ∨ (((True ∨ (p5 → p5)) ∧ (p3 ∨ True)) ∨ True))) → (p5 ∨ p1))) ∧ p5) ∨ (p5 → (True ∧ ((p1 → True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681265048247297761273234100970 : ((((p5 ∧ (((((True ∧ False) ∨ p2) ∨ ((p1 ∧ (p2 → (p3 → p4))) ∨ p4)) ∨ True) ∧ (False ∨ p4))) → ((p3 ∨ (True → False)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259937387406378531654315091856 : ((p1 → p5) → ((((p2 → (p5 ∨ (False ∨ (p2 → p4)))) → p2) ∨ (((p5 ∨ p1) ∧ p1) → p3)) ∨ ((p1 ∧ p4) → ((False ∨ p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116203084439887098282874960920 : ((((False → False) ∧ False) ∨ ((p2 ∧ (((p1 ∧ (((True → p2) ∧ (False ∧ False)) → True)) ∧ p1) → ((True ∨ p1) ∧ p5))) → False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178099906724841339948820606076 : (((((((p2 ∧ p3) ∧ p3) ∧ False) → (p5 → p2)) ∧ (p5 → p3)) → p4) ∨ ((((p1 ∧ p5) ∨ (True ∧ True)) ∧ ((p3 ∧ p5) ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112257526692505547003030699754 : (((p4 ∨ ((p3 ∧ p3) → ((((p3 → (False ∧ p1)) → p4) → (((p4 ∧ p3) → (p5 ∨ p1)) ∧ (p5 → p5))) ∨ True))) ∨ p5) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_310069728459718172487083959907 : (p2 ∨ (((p2 ∨ p5) → ((p4 → ((p1 ∨ True) ∨ p5)) → (((False ∨ p4) ∧ p5) ∧ p1))) → ((False ∨ ((p2 ∨ (p3 ∨ p3)) ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28294661578863120384628891934 : ((True ∧ ((((True → p3) ∨ (p1 ∧ (False ∨ (((p2 ∨ False) ∧ False) ∧ p1)))) ∧ (True → (p3 → p1))) ∨ (((False → p2) ∨ p3) ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337098855197081093548999533728 : (p1 → (((False ∧ ((p5 → False) ∨ (True ∨ p5))) ∨ (((p1 ∧ p3) → False) ∧ (((True → p5) ∨ (p5 ∨ (p1 ∨ p2))) → False))) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219716224340563993237415164979 : ((p1 → (False ∧ (False → p2))) → (((p5 ∧ (((True ∧ False) → p5) ∧ p5)) ∧ ((p5 → p4) ∧ (False ∧ (p1 ∨ (p3 → p1))))) ∨ (p1 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180408030482748384544847710923 : (((p1 → ((((p2 ∨ p3) → (p5 → p3)) ∧ p5) ∨ True)) ∨ (True → p5)) → (False ∨ (((False → False) → p5) ∨ (True ∨ (p4 → (True → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687139023048352943175580638872 : ((((p2 → (p5 ∨ ((((True ∧ True) ∨ (True ∨ True)) ∨ ((True → False) ∨ p4)) ∨ (p2 ∨ p5)))) → (((True → (p1 ∧ False)) ∨ True) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_299218848493089918681698418722 : (False ∨ (((p3 ∧ (p2 ∨ ((p2 ∧ p1) ∧ (False → (True → ((p3 ∨ (((p4 ∧ p5) ∨ False) ∧ (True → False))) ∨ True)))))) ∨ (p1 → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312050237994967863101432741075 : (p2 ∨ (p5 ∨ ((p1 → (False ∧ (p3 → ((p1 → p3) ∧ ((True ∨ (p3 ∨ (p3 ∧ p2))) ∧ (((False ∨ p5) ∨ p3) → (False ∧ p5))))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118650990854831751376041941366 : ((p4 ∨ (p2 ∧ ((p3 ∧ ((True ∧ p3) → True)) ∨ ((p1 ∨ ((p3 ∨ p5) ∧ p4)) ∧ ((((True → False) → p1) ∨ True) → p5))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171723130898490035715001426705 : ((((((p1 ∧ (False → p5)) ∨ p4) → (p1 ∨ ((p5 ∧ p3) ∨ p1))) ∧ p2) → p4) ∨ ((p4 ∨ p4) ∨ ((p3 ∨ p4) ∨ (False → (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252995587371677732142126342756 : ((True ∧ p3) → ((((False ∨ (p2 ∧ p2)) ∨ (True → (p1 ∨ (p2 ∨ (p2 → False))))) ∨ ((((False ∧ False) ∨ p5) → (p3 → p4)) → p2)) ∨ True)) := by
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
theorem thm_5_vars_309610791580918422687986099164 : (p2 ∨ ((((p4 ∨ (((p5 ∨ (False → (p1 ∧ False))) → p5) → ((p5 ∧ ((p5 ∧ p1) → p4)) → p3))) ∧ p1) → p2) ∨ (p2 ∨ (p1 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196831671255225200796284469563 : (((p3 ∧ (((p5 ∨ p1) ∨ p3) ∨ p1)) ∧ p3) ∨ ((((((True ∨ (False ∨ p3)) ∨ p3) ∨ p1) ∧ p5) ∨ True) ∨ ((p5 ∧ (p1 ∧ p4)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338404775897722133372671854874 : (p1 → (((p2 ∧ (False ∧ p1)) → p4) → ((((((p3 ∨ p1) ∨ p4) ∨ p5) ∨ False) → (p2 ∨ False)) ∨ (False ∨ ((p5 ∧ p2) → (p2 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



