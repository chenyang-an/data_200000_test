variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193912336080586912318070243144 : ((p1 ∨ ((p1 ∧ ((False → p3) ∧ p1)) ∧ (p3 ∨ p5))) → ((p1 ∧ ((p1 → p4) ∨ ((p3 ∨ False) ∧ False))) → (((p5 ∧ p2) ∨ True) ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h14 =>
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
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615494385171282029120610681905 : ((((((p3 ∨ ((((False → p3) ∧ (p3 → p4)) ∨ (p5 ∧ p5)) ∨ (False ∧ p1))) → p4) → ((p5 → False) ∨ (p4 → (True ∧ p3)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54006096955768041499837502318 : ((((((True ∨ (p2 → p3)) → p1) ∧ (p3 → True)) → p3) → ((((p1 → (False ∨ (True ∧ (p1 → (False ∧ p5))))) ∨ p1) ∧ p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801365047186199422670618486500 : (((p2 → (((((p1 → (False ∨ p5)) ∨ (p2 ∨ p1)) ∨ p2) → (p2 ∧ p5)) ∨ ((p3 ∨ (p1 ∧ (p5 ∧ (False ∧ p1)))) ∨ (p4 ∨ p2)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204561761044038625401279923128 : ((((p1 ∧ False) ∧ (False → p5)) ∨ p2) ∨ (False ∨ (p1 ∨ (True ∧ (p1 ∨ ((((p2 ∧ (True → p2)) ∧ (False → p4)) ∧ False) → (True ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245769858604524606747746530072 : ((p3 ∧ p3) ∨ (((p3 ∧ p2) ∨ (False ∨ ((False → True) ∨ ((p5 → (((False ∧ (p2 ∨ (True ∧ False))) ∧ p2) → (p1 ∧ p4))) ∨ True)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_677555560185204075461021162577 : (((((p4 ∨ ((p3 ∨ p4) → (p3 ∧ (p2 ∨ ((p4 ∧ (p3 ∨ (p1 ∨ (p1 ∨ p2)))) ∧ True))))) ∨ True) ∨ (((True → p5) ∧ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118795890102824502221441839268 : ((p5 ∨ (p5 → ((p4 → (p5 → p3)) ∧ (((((p2 ∨ (p3 ∨ ((p3 ∨ p1) ∨ (False → False)))) → True) ∨ False) → p2) → p4)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308445391683179538612154044442 : (p2 ∨ (((((p4 → (p1 ∨ ((((p4 → True) ∧ False) → (((p4 ∧ p2) → p2) ∧ True)) → (p3 ∨ p2)))) ∧ True) ∧ p1) ∧ (p4 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323887833118717203296616386241 : (p5 ∨ (((((p3 ∧ (p5 ∧ (False → (p1 → ((True → True) ∧ p5))))) ∨ p1) → p2) ∨ p4) ∨ (((True ∧ True) ∧ (p4 ∧ (False ∧ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39698976508189475302007842905 : (((p4 ∨ (p5 ∧ ((((False → p5) → (((p4 → True) → (p5 ∨ ((False ∨ (False ∨ p5)) ∧ p1))) ∨ p4)) → (p5 ∧ p3)) ∨ p1))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42351983608845134786646181762 : (((p3 ∧ (((p4 ∨ p4) → p2) ∧ (((True ∨ True) → (p5 → p1)) ∧ ((p2 ∨ (((p4 → p1) → (p3 → p5)) ∨ p1)) ∧ True)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66562305502961829368706141926 : ((True → ((((p4 ∧ True) ∧ ((p5 → (p5 → (((p5 ∧ ((p3 ∧ p1) ∨ (p4 ∧ False))) ∨ p4) ∨ False))) ∨ p4)) ∨ True) ∨ (p5 → p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620707654541677099003667955328 : (((((p2 ∧ p2) → (((True ∧ p2) ∧ ((True ∧ ((p3 → (p4 ∨ (((p2 ∧ True) ∨ (p2 ∧ False)) ∧ p5))) ∧ p3)) ∨ True)) ∧ p3)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215499008764009105751888896379 : ((p4 ∧ ((p4 ∨ p4) ∨ True)) ∨ (p3 ∨ ((((p1 ∧ (p1 ∨ ((False ∨ p1) ∨ p1))) ∨ (False → ((p1 ∨ True) ∧ p5))) ∨ (p5 ∨ p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42112196990498746173244952030 : ((((p4 ∧ True) → ((p1 → (((((False → (True ∧ False)) ∧ ((True ∧ (p2 ∨ p2)) ∨ p5)) → False) ∧ (p4 → p3)) ∧ p2)) → p5)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252773942604804593817695506271 : ((True ∧ True) → ((((False ∨ p4) ∧ (p2 ∨ (False ∧ (False ∧ (True → p4))))) ∨ p4) ∨ (((p2 → p2) ∧ p5) ∨ (True → ((p2 ∨ p2) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251565514861122796416447808409 : ((p3 → False) ∨ ((p5 ∨ (p1 ∨ (p5 ∨ p3))) ∨ ((((p3 ∧ False) ∧ False) ∧ (True ∧ ((p1 ∨ p3) → (False ∧ (p1 ∨ p5))))) → (p2 ∧ False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50088958678772945061888919042 : (((p2 ∧ ((p5 ∧ ((p4 ∨ (False ∨ (False → (True ∧ (p2 → (p1 → (True ∧ p2))))))) ∧ p5)) ∧ p2)) ∧ (True ∨ (p2 ∨ (False ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252013277080314286144900626671 : ((p4 → False) ∨ (p3 → ((((((True → p1) → ((p1 → (p2 ∧ (False ∧ p3))) ∨ p2)) → p1) → ((p2 ∨ True) ∨ (p5 ∨ p1))) ∧ True) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135386195940764070586252935546 : ((((False ∨ (((True ∨ ((p5 ∨ p1) → ((True ∧ False) ∨ (p3 → p4)))) ∨ p2) ∨ p5)) → p3) ∨ ((True ∨ p5) ∨ p4)) ∨ (p4 ∨ (p3 ∨ p5))) := by
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
theorem thm_5_vars_315241380823946321285812353746 : (p3 ∨ ((((False ∧ True) → p4) → p2) ∨ ((((p4 ∧ (p4 → p5)) ∧ (p4 → (p2 ∨ False))) ∧ (p5 ∨ (p3 ∨ (p3 → True)))) → (p1 → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h13 := h8 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h16 := h8 h15
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67384164013629448632769836168 : ((p1 → ((((p2 → p3) → p3) ∧ ((False → (p3 ∧ (p5 → p4))) ∨ (p5 ∨ ((((p1 ∨ (p3 ∨ p5)) ∨ p4) ∨ False) ∧ p3)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113248150780002881433290902724 : ((((((p4 ∧ ((p1 → p1) ∧ (False ∧ (False → p3)))) ∧ ((p2 → (p1 → p4)) ∨ p5)) ∨ p1) ∨ (p2 → p1)) ∧ (p2 ∧ p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111572343868355109715770940446 : (((((True ∨ p5) ∧ ((((p2 → ((p2 → ((p4 ∨ p5) → p3)) ∨ False)) ∨ p5) → (p2 ∧ p1)) → (True ∧ p4))) ∧ p1) ∨ p1) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137051509093418556881936458571 : (((p1 → p1) → (((p1 ∧ (p2 → (((p3 ∧ (p5 → ((p3 → True) ∧ False))) ∨ (p5 ∨ True)) → p5))) ∧ p3) ∧ p1)) ∨ ((p2 ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629855546415322929040257618686 : (((((((True ∨ p4) ∨ (p4 ∧ ((p1 → (False ∨ p3)) ∧ p1))) → (((False → p3) ∨ (p5 ∧ ((False → p5) ∧ p5))) ∧ True)) ∨ True) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353563125051768223301369885426 : (p4 → (p3 ∨ ((p1 ∧ (p2 ∧ p5)) ∨ (p2 ∨ ((((p4 ∧ True) ∨ (p4 ∧ (((p5 ∨ (p1 ∧ (False ∨ True))) → True) ∧ p5))) → True) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303778376287450941829538138085 : (p1 ∨ (((p4 ∨ ((p5 ∨ ((p2 ∨ p3) ∨ ((((p5 → p4) ∨ ((True ∧ p1) ∧ p4)) → p5) ∧ p4))) → (p1 ∨ (p3 ∧ p2)))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727220462891220042173283015343 : ((((False ∧ (p2 ∨ p3)) ∨ ((p4 ∧ (p5 → ((((p2 ∨ (p5 ∧ False)) → True) → (((p2 → p3) → False) ∨ p1)) → (True ∨ p1)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102717627116862657580654441934 : (((((False ∨ ((p1 → p4) ∨ True)) → (((((False ∨ True) → ((p5 ∨ (p5 ∧ p2)) ∨ p5)) ∨ p3) → True) → p1)) ∨ p2) ∨ True) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187233256259029444827577528566 : (((p5 → p5) → (True → ((True ∨ False) ∧ ((p1 ∧ True) ∧ p4)))) → (p1 → (((p4 ∧ (p1 ∨ (p5 ∧ (False → p2)))) → p1) ∨ (p2 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138224769042842614739007055796 : ((p2 → ((((p2 → p1) → p5) ∧ (((((p2 → p5) ∨ ((p3 ∨ p5) ∨ True)) ∧ False) ∨ p4) ∧ False)) ∧ (p1 ∧ p5))) ∨ ((p3 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114645282913753172743495490299 : (((((((((p5 ∨ (p4 ∧ p5)) ∨ p1) ∧ p2) ∨ False) → p3) ∧ True) → (p2 ∧ p1)) ∨ ((p4 → (False ∧ False)) ∧ (p3 ∧ p2))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693906564881524169609424698680 : (((((((((p5 → p4) → False) ∨ p3) ∧ (False → p3)) ∨ p3) ∧ (p5 ∧ False)) ∨ (p3 ∨ ((True ∧ True) ∨ (((p3 ∧ p3) ∨ p3) ∧ True)))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233975631293562261252318960037 : ((p5 ∨ (p4 ∧ p1)) → (p1 → (((False ∧ False) ∧ ((False ∨ True) ∧ (p4 ∨ p5))) ∨ (((p3 → (p3 ∧ (p2 ∧ False))) ∧ (False → p3)) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196784696556245815847529025476 : ((((False → True) ∧ (p5 ∧ (p3 → p2))) ∧ p2) ∨ (((p2 ∧ (((False ∨ p3) → (p1 ∨ p4)) ∨ True)) ∧ ((p2 → False) → (p3 → p4))) → p2)) := by
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
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112045299018461613006117100306 : (((((True → p1) → p1) → ((False ∧ p1) ∨ ((((p5 → p4) ∨ p3) ∨ ((((p1 → p3) → p5) ∧ p4) ∧ p2)) → False))) ∨ False) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88012474147892025038939045901 : (((((p3 → True) → False) ∧ True) ∧ ((((((p5 → p5) → p4) ∨ (p4 ∧ (False → p2))) ∧ (((p4 ∧ p3) ∨ True) ∧ p3)) → p2) → p5)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147537595711885404356551575999 : (((p2 → (((((p1 → p3) ∨ (p3 → ((p3 → False) ∧ (p3 → p2)))) ∧ (False ∧ p1)) ∧ False) ∨ p1)) ∨ p4) ∨ (True ∨ (p2 ∨ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300810366658317371767263390703 : (False ∨ (((p5 ∨ ((p3 ∨ (p5 ∨ (((True ∨ (p3 ∨ p5)) ∧ p5) → False))) ∧ True)) → p3) → (((p5 ∧ p3) ∧ (False ∨ (p2 → p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105776049252245295939836036433 : ((((((((p2 → (p3 ∧ p1)) → (False ∨ (p2 ∨ True))) ∨ False) → False) → True) ∨ False) → ((True → (p3 → False)) ∨ (False → p5))) ∧ (p3 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41326195214557051304267686131 : ((((p4 ∨ (((True ∧ False) ∨ ((p1 ∨ p3) → (p3 ∨ p2))) ∨ (p4 ∨ (True ∨ False)))) ∧ ((p4 ∧ p4) → (False → (p2 ∨ p5)))) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175162735334513994635547456234 : ((True ∨ ((p5 → (((p1 ∧ p2) ∧ ((p4 → p1) ∨ (p5 ∧ p4))) ∧ p5)) ∨ p4)) → (p1 → (p3 ∨ ((p4 → (p5 → (True ∧ p5))) → p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343572862321033284563042727552 : (p2 → ((True → False) → ((p5 ∨ (p5 ∧ (((((True → p2) ∨ (True ∧ True)) ∧ (False → True)) ∨ ((p5 ∧ False) → True)) → p1))) ∨ (True → p5)))) := by
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
theorem thm_5_vars_227574043499524158002668912971 : ((False ∧ (True ∧ p5)) ∨ (p2 ∨ ((((p3 ∨ (((p4 ∧ (((p4 ∨ p2) ∨ p4) ∨ (p2 ∨ p2))) → p1) ∨ p2)) → (p3 ∧ False)) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309846921865642321820135326724 : (p2 ∨ ((((p1 → p1) ∨ (p4 → (p5 ∧ (p2 → p1)))) ∨ (p4 ∧ (p1 → ((True ∨ (p3 → p2)) ∨ p1)))) → ((p5 ∨ (p5 ∨ p5)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h6 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722087839882063959356581115006 : ((((p2 → ((p2 ∨ p3) → p3)) → (((p2 ∨ ((p2 ∨ p1) ∨ False)) ∧ p3) ∨ ((p3 → (p2 ∨ (True ∨ False))) ∧ (p5 → (p5 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43761075257101944184302105036 : ((((p2 ∧ (p2 ∨ (p4 ∨ (p1 ∧ ((((False ∧ (p3 ∨ p2)) → p4) ∧ (p5 → (p1 ∨ ((True ∧ p3) ∧ True)))) → p3))))) → p1) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261652577807711231182926868132 : ((p5 → p5) → ((p4 ∨ p5) ∨ (((((((p2 ∧ p5) ∨ True) → (p1 ∨ (p2 → p3))) → False) ∨ True) ∨ ((p5 ∧ p3) → False)) ∨ (p5 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_55054363639106371582224087843 : (((p1 ∨ (((True → False) ∧ p2) ∨ p1)) ∧ ((((False ∧ ((True → False) → True)) ∧ (p2 ∨ ((p5 ∧ (p3 ∧ p2)) → p1))) → p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311805706256284392041528942149 : (p2 ∨ (p1 ∨ (((p4 ∨ p1) ∧ (((False ∧ p4) → (p5 ∨ p3)) ∧ (p3 ∨ ((p5 ∨ (True ∨ (p2 ∨ p3))) ∨ (p3 ∧ (False → p2)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3026315764079185774128036006 : ((p1 ∧ (p1 → False)) → (p2 ∨ (p2 ∧ (((p5 → p4) ∧ (False ∨ (p3 ∨ (p5 → (p4 ∧ ((False → True) → p3)))))) → (p4 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184402195756898337589253477445 : (((((p2 ∨ p5) ∨ (p3 → (p5 ∨ p1))) ∧ p3) ∧ (p1 ∧ True)) ∨ ((p5 ∧ ((((False ∨ p2) ∨ p4) → p4) ∧ ((p4 → p4) ∧ p3))) → p3)) := by
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
theorem thm_5_vars_40932732870051525502339831873 : ((((((((p5 → (False ∧ p5)) → (((p3 → p2) ∧ (p2 → True)) ∨ ((p3 ∨ p5) → True))) ∧ p1) ∧ p2) ∨ p4) ∨ (p4 ∧ p5)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769178954440291028750526945661 : (((p5 ∧ ((False ∧ p3) ∨ (p1 ∧ ((p3 ∧ ((p4 ∨ p1) ∧ (p5 ∧ ((((p4 → ((p4 ∨ True) ∧ p3)) → p5) → p1) ∧ p1)))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342294985396419917863886175840 : (p2 → (((p2 ∨ p5) → (p5 ∨ ((p3 → ((p5 ∧ p1) → ((False ∧ p3) ∧ (p5 → True)))) ∧ True))) ∨ ((p5 → p3) → ((True → p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118144152780496758415543011108 : ((False ∨ (((p5 ∨ ((p5 ∨ (False ∧ p2)) → p5)) ∧ (p3 ∧ (False ∧ p2))) ∨ ((p4 ∧ p4) → ((False → p5) ∧ (True ∨ p2))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299514795994280901059771517493 : (False ∨ (((((p5 ∨ (p1 ∨ (p2 ∨ (p3 ∧ (((p1 ∧ p2) ∧ ((p3 → p1) ∧ (p4 ∨ p1))) ∧ p3))))) ∨ (p5 ∨ True)) → False) ∧ True) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ (p1 ∨ (p2 ∨ (p3 ∧ (((p1 ∧ p2) ∧ ((p3 → p1) ∧ (p4 ∨ p1))) ∧ p3))))) ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135267407677482597941872973063 : (((True ∨ ((p1 ∧ p3) → ((p1 ∨ p1) ∧ (p3 → (((p1 ∨ p2) ∨ (p5 ∧ p1)) ∧ (p4 → p1)))))) → (False ∧ True)) ∨ ((p4 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39739537061536761802157113505 : (((p5 ∨ (False ∨ (((True ∨ ((p2 ∧ p2) ∨ (True ∧ (((p4 → False) ∧ p4) ∨ p5)))) ∨ p5) ∧ ((p2 ∨ p4) ∧ (p5 ∨ p3))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42244000547194324431207504504 : (((False ∧ (p2 ∨ ((((p4 ∧ ((p3 ∨ p5) ∨ (p5 → p3))) ∧ p2) ∧ (p2 ∨ (True ∧ p4))) ∧ (((p3 ∨ True) ∨ True) ∧ p4)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305002658143096090513563101737 : (p1 ∨ ((((((p1 ∧ (True ∧ p5)) ∨ (((p3 → True) → p3) → p5)) → p3) ∧ p4) ∨ (p4 ∨ ((p2 → p3) → p4))) ∨ (False → (p3 ∧ p1)))) := by
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
theorem thm_5_vars_753486899989859565166609754068 : (((False ∧ ((p4 → (((((False ∨ (False ∨ (False ∧ False))) ∨ (True → (p4 → (p4 ∨ p4)))) ∧ p3) ∨ p3) ∨ p4)) → (p3 ∧ (True ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111754086588544740101594181735 : ((((((p3 → ((p5 → False) ∨ (p3 ∧ ((p4 → (p1 ∨ False)) → (True ∨ (False ∧ p2)))))) ∧ p3) ∧ p1) ∧ (p5 ∧ False)) ∨ p1) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698330443687373707074741057363 : ((((((p5 ∨ ((p2 ∨ False) ∨ (p3 ∧ p3))) ∨ p5) ∨ (True → False)) ∨ (False ∧ ((False ∨ p2) → (True ∧ (p3 ∧ ((p1 ∨ p5) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224609429351986796985156922685 : ((p2 → (p4 → p4)) ∧ (((p1 ∧ p1) ∧ ((((((True ∨ (p1 → p4)) ∨ (p4 ∨ False)) → (p1 ∧ p4)) ∨ p4) ∨ p4) ∧ True)) ∨ (True ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350916027137972936893268851122 : (p4 → ((((p5 → (((p1 ∧ p3) ∧ p1) ∨ (((p4 → (((True ∨ p3) ∨ False) ∧ p1)) → (True → p3)) → p3))) ∨ True) ∨ True) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246771002974487390874690088760 : ((p5 ∧ p5) ∨ ((False ∨ (False → True)) → ((((True ∧ (p4 ∧ (True → p1))) ∨ (p3 → p5)) ∧ p1) → (p4 → (p5 ∨ (p3 → (False ∨ p4))))))) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179452306282946107264402535257 : ((p5 ∨ (((p5 ∨ (p3 → p1)) → p3) ∧ (p2 ∧ (p4 ∧ (p2 ∧ False))))) ∨ (True ∨ (p3 ∧ (((p5 ∧ (p2 → (p4 ∧ True))) → p1) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123111054575676123224592897107 : ((((p4 ∨ ((((False → (p4 ∨ p1)) → (p2 → (p1 ∨ True))) ∧ False) ∨ p5)) ∨ (p1 ∧ (p4 ∨ p1))) → ((p1 ∨ True) ∧ p2)) → (p1 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∨ ((((False → (p4 ∨ p1)) → (p2 → (p1 ∨ True))) ∧ False) ∨ p5)) ∨ (p1 ∧ (p4 ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628822092395088201148798690991 : (((((p3 → (p3 → (p3 → ((False ∨ (p4 ∧ (False ∨ False))) → (((False ∨ (p5 ∨ False)) ∨ p2) ∧ (p3 ∧ (p1 ∨ p5))))))) ∧ p2) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117206257577220273206660628363 : ((True ∧ (((p3 ∧ True) → (((False ∧ True) ∨ p2) ∨ p5)) → ((((True ∨ (False → True)) ∧ (p2 ∨ False)) ∧ p1) ∨ (p5 → p1)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312396922061058432304595044331 : (p2 ∨ (p3 → (p4 ∨ (((p2 ∧ (p5 ∨ p2)) ∨ False) ∨ (((((p5 ∨ (p1 → False)) ∨ ((p1 → p2) ∧ (p5 ∨ False))) ∧ p2) → p4) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47658335747491237811418597877 : ((((((False ∨ (((p3 ∨ p4) ∧ p5) ∧ ((p4 ∧ False) ∨ p4))) ∨ (p1 ∨ p3)) ∧ (True → ((p5 → p1) ∧ p3))) ∧ p1) → (p3 ∨ p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h26 := h5 h25
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337068790191142788110434094478 : (p1 → (((((p4 → p1) ∨ p1) → (p5 ∧ ((p2 ∨ (((p4 ∧ p2) ∨ p1) ∨ (p2 ∧ p1))) ∨ (p4 ∨ p1)))) ∧ (p3 ∨ p2)) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214345776669989081574314841411 : (((p2 ∨ (p5 → p1)) → p2) ∨ (p2 ∨ (p5 ∨ (True ∨ ((p1 ∧ (((p3 ∧ (p3 ∧ p1)) ∨ p1) → ((p5 ∧ p3) ∧ p5))) → (p4 → False)))))) := by
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
theorem thm_5_vars_147897861577392423404394708996 : ((((p2 ∧ (p1 ∨ (((p4 ∧ p2) ∧ ((p4 ∨ p5) → (False ∧ p2))) ∧ (p4 ∧ p2)))) ∨ p2) ∧ (True → p2)) ∨ ((p3 ∨ (False → p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163120708761632172505250833866 : ((((((p2 → True) → False) ∨ ((True → p4) ∨ p3)) ∧ p2) ∨ ((p2 ∨ True) ∨ (True ∧ p5))) ∧ ((((p2 ∨ p2) → False) → True) ∧ (True → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206102186621247825155572831758 : ((p4 ∧ (((p4 → p4) ∧ p1) ∧ p1)) ∨ ((p5 ∧ (p2 ∨ ((p4 → False) ∧ p1))) ∨ (((p5 → (p2 → (p4 ∨ p4))) → True) ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_142354889581786616409253171160 : ((p3 ∧ (p1 ∧ (p4 ∧ ((((p3 ∧ ((True ∨ p2) → p2)) ∧ ((p2 → (p1 ∨ p2)) ∨ (p3 ∧ p2))) ∧ p4) ∨ False)))) → (p2 ∨ (p3 → False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h15 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768852635121100054326534275109 : (((p5 ∧ (((((p5 ∧ p4) ∨ p5) ∨ p2) → True) → (p2 ∧ ((((p3 → p2) → (p5 ∧ p3)) ∨ p3) ∨ ((p5 ∧ p1) → (p4 ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893110672946755508074870884389 : (((((((((False → True) ∧ ((True → p5) → p4)) ∨ True) ∨ p2) → False) ∧ (p1 → ((True ∧ (p2 → p2)) ∨ False))) ∧ ((False ∧ p2) ∨ p4)) → p3) ∧ True) := by
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
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : ((((False → True) ∧ ((True → p5) → p4)) ∨ True) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175262345825178678376224262291 : ((p2 ∨ ((((p2 ∧ p1) ∧ p2) ∨ False) ∨ (((p3 ∧ p5) → (False ∧ p2)) ∧ True))) → (((False ∨ p1) ∨ (p3 → p3)) ∨ (False ∧ (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730094014238048515078869223917 : (((((p3 ∨ False) → p4) → (((((p5 → ((p3 ∧ False) → p4)) → (((p3 → (p1 ∧ p1)) → p3) ∧ p2)) → p1) ∧ True) → (p1 → p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2198332105431337956050836427 : ((p1 ∧ (((p1 ∧ False) → p2) ∧ (p3 ∨ (((p2 ∧ (p1 → False)) ∧ p2) → p3)))) ∨ (p1 → (((p2 → (p3 ∧ p1)) → p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256744808868530183808830558967 : ((p1 ∨ p1) → (p3 ∨ (((p3 ∨ (p2 → (((False → (False ∨ (p4 → p5))) → p5) ∨ False))) ∨ (p1 → (p4 → True))) → ((p5 ∧ p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43037473270939518003183015836 : ((((((((p1 ∧ True) ∧ False) ∨ p2) ∧ (p5 ∨ (p4 → (((p2 ∧ p5) → (True ∨ (p4 → p2))) ∨ (True ∨ p3))))) ∨ p1) ∧ p3) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749726571772199260920105053139 : (((True ∧ (((True → (p1 ∨ (((True → ((True ∧ p2) ∧ (p3 ∧ False))) → p4) → True))) → (False ∧ ((False ∧ (False ∧ False)) ∨ True))) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50521421998256428675469818196 : ((((False ∨ (((p2 ∧ ((p2 ∨ True) ∧ ((True ∧ p3) → (p4 → True)))) ∨ (p4 ∧ p5)) → True)) ∧ True) → (p4 ∨ (p3 → (p4 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233584937220555049994514431918 : ((p1 ∨ (p4 → p5)) → ((True ∧ ((p4 ∨ p2) → p1)) ∨ (True ∨ ((p4 ∧ p2) ∨ ((((p4 ∧ False) ∧ (p3 ∨ p5)) → (p4 ∧ p1)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324856589616371324958209236538 : (p5 ∨ ((p1 → p1) ∧ (((p5 → (((p1 ∧ (True → p2)) → p1) → (p2 ∨ (((False → p4) → p3) → False)))) ∨ True) ∨ (p1 ∨ (p1 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110841144136034860866515487060 : ((((p4 ∨ (((p5 ∧ p1) ∧ (p3 ∨ (((True ∧ p4) ∧ ((p1 ∧ p3) ∧ p4)) ∧ (p5 → p1)))) ∨ (p1 ∨ True))) ∨ p4) ∧ True) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161123346815714223360884085935 : (((p5 ∨ p4) ∧ (((((p4 ∨ ((p2 ∨ p2) ∧ p4)) ∨ False) ∧ p1) ∨ (p4 ∨ p5)) ∨ (p5 ∨ p2))) → ((p4 ∨ False) → ((p3 ∨ p2) ∨ p4))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h12
            case inr h13 =>
              -- Conjunctions on the left can always be decomposed.
              let h14 := h13.left
              let h15 := h13.right
              -- Disjunctions on the left can always be decomposed.
              cases h14
              case inl h16 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h15
              case inr h17 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h15
          case inr h18 =>
            -- False on the left can always be used.
            apply False.elim h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h30 =>
            -- Disjunctions on the left can always be decomposed.
            cases h30
            case inl h31 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h31
            case inr h32 =>
              -- Conjunctions on the left can always be decomposed.
              let h33 := h32.left
              let h34 := h32.right
              -- Disjunctions on the left can always be decomposed.
              cases h33
              case inl h35 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h34
              case inr h36 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h34
          case inr h37 =>
            -- False on the left can always be used.
            apply False.elim h37
        case inr h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h39
          case inr h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h25
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h25
  case inr h44 =>
    -- False on the left can always be used.
    apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157525930928550713066221848640 : (((p4 → ((p5 ∨ ((p1 ∨ ((False → (p5 → p4)) → (True ∧ True))) ∧ p1)) ∨ False)) ∨ (p4 ∧ p4)) ∨ (p3 ∨ ((p2 → p2) ∧ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142966534213281227114663365037 : ((True → ((((p4 → (True → (((p3 → p1) → p3) → p5))) ∧ (True ∨ (p1 → ((True ∨ p4) → p5)))) ∧ p1) ∧ p4)) → (p2 → (False ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136397590117399683580728797654 : (((False ∨ (p1 → (p1 → p5))) ∨ ((p2 ∨ (((p5 → (p4 → (p5 ∧ (p5 → False)))) ∨ p3) ∨ p1)) ∨ (p2 → p2))) ∨ (p2 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153709080047960478622427092264 : ((p3 → ((((True ∨ (((((p5 → True) → False) ∧ p3) ∨ (p5 ∨ (p1 ∧ p4))) ∨ p3)) ∨ p3) ∨ p1) ∨ p3)) → ((p2 → False) → (p2 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56918845432636939288215527562 : (((p5 ∧ (p3 → p3)) ∧ (((p1 ∨ ((((False → p1) ∧ p5) ∨ p2) → (False ∨ (True ∨ (((False → p4) ∨ p4) ∨ p2))))) ∨ p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61919136203918450507779308153 : ((p2 ∧ (((((p2 ∧ p3) ∧ (((p5 ∨ p2) ∨ ((p5 → (p4 → p1)) ∧ p4)) → p1)) → (False ∧ p5)) ∧ p1) → (p2 ∨ (p2 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



