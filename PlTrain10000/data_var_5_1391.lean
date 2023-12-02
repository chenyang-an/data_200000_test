variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198413477178258477896069207005 : ((p4 ∧ ((p2 ∧ ((False ∧ p5) → p4)) → p5)) ∨ (True ∧ ((p3 ∨ (p3 ∨ (False ∧ ((p1 ∧ p4) ∧ p1)))) ∨ ((p1 ∨ False) → (p1 → p1))))) := by
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
theorem thm_5_vars_184711894651354395925371177870 : ((((p5 → p3) ∧ (p5 → (False → False))) → (True ∧ (False ∨ p3))) ∨ (p1 → ((((p5 ∨ p3) → ((p2 ∨ (p5 ∨ p2)) → p1)) ∧ p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65662671916347455044046419860 : ((p4 ∨ (((True ∧ (((False ∧ p4) ∧ p2) → ((p2 → ((p3 ∧ (p1 ∧ p4)) ∨ p1)) ∧ (((True → p4) ∧ p5) → True)))) ∧ True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593981764421898332501164915597 : (((((True ∧ ((p1 ∧ (False → p3)) → (p4 ∨ (p1 → ((p4 ∨ (p2 ∨ (p2 ∧ p2))) ∧ p1))))) ∨ (False ∨ (p1 ∧ (p1 ∧ p4)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230826818441472037343127491575 : (((False ∧ p4) ∨ p2) → (((((True → (p1 ∨ p5)) ∧ (True → p4)) ∧ (((((p2 ∧ False) ∧ True) → p1) ∧ p1) ∧ (False ∧ True))) ∨ p2) ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57246269432585834848709315581 : ((((p3 ∧ p4) → p2) ∨ (((p4 ∧ ((p1 ∨ (p4 → p1)) ∧ ((False ∧ p5) ∧ ((p1 ∧ p4) → p5)))) ∨ (True → p5)) ∨ (p1 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685996661943456129196502022115 : ((((((p4 → (p4 → (p5 → p5))) → (False → ((p5 → True) → (p5 ∨ p1)))) ∨ (True ∧ True)) → ((p5 → ((True → p1) ∧ p4)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52801714503392249550471210220 : (((((((p3 ∧ p2) ∧ p5) ∧ p1) → (p5 → p5)) → ((p4 ∧ p3) → p2)) → (False ∨ (((p2 ∧ p4) ∨ p2) ∨ (p2 ∨ (p5 → p5))))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112703096981545956863974476760 : (((((((((True ∨ ((True → p4) ∧ p1)) → (False → p4)) ∨ p5) → p1) ∧ p3) → False) → (p2 → ((p4 ∨ False) ∧ True))) → p5) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392849354388868155201650565044 : ((((((p2 → p4) → False) → (((((p1 ∧ (p4 ∧ False)) → p1) → True) → False) ∧ ((p4 ∧ ((True → False) → (p4 ∧ p5))) → p1))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_44485254042196224986398219515 : ((((p5 → (p1 ∨ ((p2 ∨ ((p4 → p2) ∧ p2)) ∨ (False ∧ False)))) → ((False → p2) ∧ ((((True ∧ p4) ∧ p2) ∧ p5) → True))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41524364041687008632315831232 : ((((False ∧ ((p4 ∨ (True → p1)) → ((True ∨ p3) ∨ p3))) ∧ ((p5 → ((p2 ∨ (p2 → (p2 → (p1 ∨ False)))) → p2)) → p3)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310892263216282409511426500792 : (p2 ∨ ((p3 → (p3 → p5)) → ((p4 ∧ ((p5 ∧ p2) ∧ (p4 ∨ ((p5 → (p2 ∨ (p5 ∨ p2))) → (False ∨ True))))) → (p5 ∨ (p5 ∧ False))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199283491141713255024947728135 : ((((p4 ∧ (p2 → (p4 → True))) ∧ p4) ∨ False) → ((p4 → (((p2 ∨ False) ∧ (((False ∨ ((p3 ∨ p5) ∧ p3)) ∧ p4) ∧ p2)) ∨ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92945170211254958016062130637 : ((True ∧ (((True → (True ∧ False)) → (p3 ∨ ((p5 → (((p2 ∧ p1) ∧ ((((p5 ∨ p4) ∨ p3) → True) ∧ p2)) → p4)) ∧ p5))) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → (True ∧ False)) → (p3 ∨ ((p5 → (((p2 ∧ p1) ∧ ((((p5 ∨ p4) ∨ p3) → True) ∧ p2)) → p4)) ∧ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172516258024124790842735214532 : ((((p5 ∨ p3) → p2) ∧ (p2 → ((((True → p5) ∨ (p3 ∨ p3)) ∧ p4) ∨ False))) ∨ ((p5 ∨ (p3 ∨ ((p4 ∧ p2) ∧ p1))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2751561702888641840182248933 : ((True ∨ (p3 → (False ∨ True))) ∧ (p5 → (p4 → (p3 ∨ (((p2 ∨ ((p1 ∨ p3) ∨ p4)) ∧ p3) ∨ ((False ∨ (True ∧ p2)) → p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632753306793169913446982676496 : ((((((((p4 ∨ p5) ∨ ((True ∨ ((p1 ∨ (p2 → p4)) → p5)) → p1)) ∧ (p1 → (True ∨ (p1 ∨ p2)))) ∧ p1) ∧ (p4 ∧ True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230902919820842854354202508116 : (((p2 ∧ p3) ∨ p5) → (p1 ∨ ((p1 ∨ (((p2 ∨ (p4 ∧ p1)) ∧ (p2 → (((p2 ∨ False) → p4) ∧ (p5 ∧ (True ∨ p1))))) ∨ p3)) ∨ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226065472782163672522639099234 : (((p5 ∧ p4) ∨ p3) ∨ (p5 ∨ ((p2 ∨ (True ∨ (((p1 → (((False → ((False ∨ True) ∨ p5)) ∧ p3) → p2)) ∧ (p2 → p2)) → p3))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178260577915210749422741194592 : ((((p3 ∧ (p3 ∨ ((p3 ∧ False) ∧ p2))) ∧ (True ∨ False)) ∧ (p2 ∧ p2)) ∨ ((False ∧ ((False ∧ p3) ∧ p1)) → ((p2 ∨ p1) ∨ (p5 ∨ p2)))) := by
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
theorem thm_5_vars_204361749665961856544817837698 : (((p2 ∨ ((p4 ∨ p4) ∨ False)) ∧ True) ∨ (p3 → ((((True ∧ (p1 ∨ p5)) → p2) → (p1 ∨ False)) ∨ ((True ∧ (p4 ∨ p1)) → (p4 ∨ p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301509972023567830629748536398 : (False ∨ ((p1 → (False ∨ p1)) ∧ ((True ∧ ((False ∨ (p5 ∨ (p2 → p5))) ∧ (p4 ∨ (p2 → p4)))) ∨ ((True ∨ (True → (True ∨ p5))) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1484752519623610619690995754 : ((((p2 ∨ p1) → (p2 → (p3 ∧ (True ∨ (((((p1 ∨ p4) → p2) ∨ (False ∧ False)) → False) → (False ∧ p3)))))) → p2) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310203670423113260805529887330 : (p2 ∨ (((((p5 ∨ True) ∨ True) → ((p1 ∨ p1) → (p2 ∧ p5))) ∨ p2) ∨ (True → (p3 ∨ ((p3 ∧ p1) ∨ ((False ∨ False) → (p4 ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347060163154612229142265565967 : (p3 → ((p4 ∨ ((((p1 → False) → p2) ∨ (((False ∧ p1) ∨ p2) → True)) ∧ (False ∨ p5))) → ((p2 → (p2 ∧ (p3 ∧ (p4 ∧ p5)))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84631585458209430198967351881 : (((False → (((((p3 ∨ (((p1 → p4) ∧ False) ∨ p2)) → p3) ∨ p3) ∧ True) ∧ p4)) → ((p2 ∨ (p1 ∧ p1)) ∧ ((p1 ∨ p5) ∧ False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (((((p3 ∨ (((p1 → p4) ∧ False) ∨ p2)) → p3) ∨ p3) ∧ True) ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147439880437867013932529077219 : ((((p4 ∨ p3) ∧ (((((True → p2) → ((p1 → p1) → (False ∨ p1))) → p3) → p2) → (p3 ∨ p3))) ∨ True) ∨ (True ∨ ((False ∧ p3) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246075762434599502638363723833 : ((p4 ∧ p1) ∨ (((p4 ∧ ((True → p1) ∧ (((p2 → ((True ∨ ((p4 → True) ∨ p4)) → p1)) ∧ ((p4 → p4) ∧ p5)) ∨ p5))) ∧ True) → p1)) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h17 := h6 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42957410584231989466820561062 : (((p4 → (p4 → (p1 ∧ ((p5 ∨ ((p3 ∨ (((p3 ∨ p3) → (((p1 ∨ False) → True) ∨ (p2 ∧ p2))) → p3)) ∨ p2)) ∧ False)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616996201064900267304726214546 : (((((((False ∧ (p3 → True)) ∨ (p4 → p1)) ∨ p4) ∧ (p5 ∧ (p3 → ((p4 ∨ p5) ∧ ((p1 ∨ ((p1 ∨ False) ∧ p1)) ∧ p2))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781202803070133381425513534327 : (((p2 ∨ ((p5 ∨ p2) → (p4 → ((True → ((True ∨ False) ∨ ((p3 ∨ (((p3 → (p1 → (p3 → p4))) ∨ p3) → False)) ∨ p1))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52730564239167486963966507616 : ((((((p2 ∧ (((p1 ∨ p4) → True) → (p3 → True))) ∧ p3) ∧ p1) ∨ p2) → (p3 ∨ (((p3 ∧ (True ∨ (p1 ∧ p4))) ∧ False) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200107314725072768183731876797 : (((p1 ∧ (p2 → p3)) ∧ ((False ∨ p4) → p3)) → (((p1 ∧ ((True ∧ True) ∨ ((p5 → p2) → p2))) → ((True ∨ p2) → p5)) → (False ∨ p5))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∧ ((True ∧ True) ∨ ((p5 → p2) → p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216479879127556290929935870163 : ((p5 → ((p4 ∨ p3) ∧ p4)) ∨ ((p5 ∧ (((p3 → ((True ∧ (True ∨ p2)) ∧ p1)) ∨ (False ∨ (True ∧ True))) ∧ p2)) ∨ ((False → p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192302582200790623375264143099 : (((True ∧ (True → ((True → (False ∧ p3)) ∧ True))) ∧ p3) → ((((p3 ∧ p1) ∨ (p4 → False)) → (p4 ∧ (p2 ∧ (p1 → True)))) ∧ (p3 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h34 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h35 := h33 h34
    -- We need to get the left conjuct of h35 based on <expert-advice>.
    let h36 := h35.left
    -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
    have h37 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h36, we can now drive its conclusion.
    let h38 := h36 h37
    -- We need to get the left conjuct of h38 based on <expert-advice>.
    let h39 := h38.left
    -- False on the left can always be used.
    apply False.elim h39
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h1.left
    let h42 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
    have h45 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h44, we can now drive its conclusion.
    let h46 := h44 h45
    -- We need to get the left conjuct of h46 based on <expert-advice>.
    let h47 := h46.left
    -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
    have h48 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h47, we can now drive its conclusion.
    let h49 := h47 h48
    -- We need to get the left conjuct of h49 based on <expert-advice>.
    let h50 := h49.left
    -- False on the left can always be used.
    apply False.elim h50
  -- Implications on the right can always be decomposed.
  intro h51
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h52 := h1.left
  let h53 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h54 := h52.left
  let h55 := h52.right
  -- One of the premise coincides with the conclusion.
  exact h53
  -- Conjunctions on the left can always be decomposed.
  let h56 := h1.left
  let h57 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h58 := h56.left
  let h59 := h56.right
  -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
  have h60 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h59, we can now drive its conclusion.
  let h61 := h59 h60
  -- We need to get the left conjuct of h61 based on <expert-advice>.
  let h62 := h61.left
  -- We want to use the implication h62 based on <expert-advice>. So we show its premise.
  have h63 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h62, we can now drive its conclusion.
  let h64 := h62 h63
  -- We need to get the left conjuct of h64 based on <expert-advice>.
  let h65 := h64.left
  -- False on the left can always be used.
  apply False.elim h65



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50429402607107160858555533794 : (((p5 ∧ ((True → ((((p3 → (p3 → p1)) ∨ p4) ∧ (False ∨ (p4 ∧ False))) ∨ (p5 → False))) ∧ p4)) ∨ (p3 ∨ ((True ∨ p4) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171449094075300471422611760643 : (((p2 ∧ ((((True → p1) ∨ p3) → (((p4 ∧ False) → p1) ∧ False)) → p1)) ∧ p4) ∨ ((p2 ∧ (True → p2)) → ((True → p1) → (p1 ∨ p4)))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316912727558447628771347698084 : (p3 ∨ (p2 → ((((False → False) → ((p2 → (p2 ∧ ((True ∨ ((p3 ∨ p2) → (p1 → True))) ∧ (p1 → True)))) → p1)) ∨ (p5 → p2)) ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249134562207646785633941903354 : ((p4 ∨ p2) ∨ ((p5 ∨ ((True → (False → p2)) → p4)) ∨ (True ∨ (True ∨ ((((False → False) → (p3 ∧ ((True → p3) → p2))) ∧ p4) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142746684039541992694635742202 : ((p2 ∨ ((p4 ∨ p2) ∨ (p4 ∨ (p4 ∨ (((((((p3 ∧ (p5 ∨ True)) ∨ True) ∨ p2) ∧ p5) → p2) → p3) ∧ True))))) → ((p1 → p2) ∨ True)) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337848370401310914211635272489 : (p1 → ((((((True ∨ ((p4 → (p3 ∨ p5)) ∧ True)) → p5) ∨ p4) ∨ p2) ∧ p3) ∨ (((((True → p3) ∨ False) ∧ False) → False) ∨ (p3 ∨ p1)))) := by
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
theorem thm_5_vars_39909951409435173929606917488 : (((p3 → ((False ∧ ((((True ∨ (((p4 → p5) ∧ (False ∧ p1)) → True)) ∨ (True → p5)) ∨ ((p1 ∧ False) ∨ False)) ∧ p1)) ∨ False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44543760275875390344257811424 : ((((p5 ∧ (False ∧ (((p5 ∧ p1) → (p3 ∨ p4)) ∧ p1))) → (True → ((p3 ∧ p2) ∧ (p5 ∨ (p4 ∧ (p2 ∧ (p5 ∨ p1))))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310877645496934418325779604578 : (p2 ∨ ((p1 ∨ (p4 ∨ p5)) → ((p1 ∧ (False → p4)) → (True ∧ (((((p4 ∧ (p3 ∧ (p1 ∧ p4))) ∧ False) ∨ True) → False) → (p5 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (((p4 ∧ (p3 ∧ (p1 ∧ p4))) ∧ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (((p4 ∧ (p3 ∧ (p1 ∧ p4))) ∧ False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : (((p4 ∧ (p3 ∧ (p1 ∧ p4))) ∧ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h21 : (((p4 ∧ (p3 ∧ (p1 ∧ p4))) ∧ False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h22 := h3 h21
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h24 : (((p4 ∧ (p3 ∧ (p1 ∧ p4))) ∧ False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h25 := h3 h24
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658208028985538223514668873632 : ((((p5 ∧ (((((p4 ∨ (p1 ∨ True)) ∨ (False ∨ (p1 → p4))) → ((p5 → False) → (False → False))) → (True ∧ p4)) → p1)) ∨ (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328167494842532561994063987805 : (True → (((False ∨ (((p2 → ((p4 ∨ ((p2 ∨ p1) → p4)) → True)) → ((p5 ∨ p5) → (p5 ∨ p2))) ∨ p2)) ∨ False) → ((True → False) → p5))) := by
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
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h9 := h3 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h11
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153168027467900925806865029529 : ((p5 ∧ (((((p3 ∨ True) ∧ p5) ∧ True) ∧ p4) ∨ ((p3 → (p2 ∧ ((p1 ∨ p1) ∨ (False ∨ p3)))) → True))) → (p2 ∨ (p2 ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799616452522204078602649814061 : (((p1 → (p5 ∨ ((False → (((p2 ∨ p5) ∧ (p2 ∨ (p1 ∧ p1))) ∨ p2)) → ((((((p4 ∨ p2) → p2) → p5) ∨ False) ∧ p2) → p5)))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p4 ∨ p2) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127542022986739995181413746130 : ((p4 ∨ (((p4 ∧ False) ∨ (((p1 ∧ p1) → (False ∧ ((True ∨ True) → False))) ∨ True)) → ((p3 ∧ False) ∧ ((p2 ∧ p3) ∨ True)))) → (p4 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∧ False) ∨ (((p1 ∧ p1) → (False ∧ ((True ∨ True) → False))) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247580049739406988159996247724 : ((False ∨ p4) ∨ (p3 → (((((p2 → p3) ∨ p5) → False) ∨ ((p1 ∧ True) ∧ (False → ((True ∧ p5) ∧ (((p1 → True) ∨ p1) ∨ False))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41888196156505218872561647772 : ((((p5 ∨ (True → p3)) ∨ (((p2 ∧ ((((p1 ∧ False) ∨ p2) ∨ True) ∨ (True ∧ p4))) ∧ p2) ∧ ((True → False) ∧ (p2 ∨ p3)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598507772895312404203544305519 : ((((((True ∧ p5) → p4) → (p5 → (p4 → ((p1 ∧ ((p3 ∧ (p1 → (p4 ∨ p2))) → p1)) ∧ ((p2 ∨ (p4 ∨ p4)) ∨ p1))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207554919952033182749847836156 : (((((p2 ∧ p2) ∨ p2) ∨ p4) → p1) → ((((p1 ∧ p5) ∨ (p4 → (False → (True ∧ p2)))) ∨ (p5 ∨ (p5 → (p3 ∨ True)))) ∨ (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258625626163592516366115291236 : ((p5 ∨ p4) → (p1 ∨ (((p4 ∨ (p4 ∨ p3)) ∨ (((p2 → False) ∨ (p5 ∧ (p2 ∧ ((p3 → (p1 ∧ (p2 → p1))) ∧ False)))) ∨ p5)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48135554840824750846669402970 : (((((False ∧ p5) → p4) ∨ (p3 ∨ ((False ∧ ((((p5 ∧ (p5 ∨ p4)) ∨ p2) ∨ True) ∨ (p1 ∧ True))) → (p5 ∧ True)))) → (p4 → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185080525889753163940216235646 : (((False ∨ p5) ∨ (p5 → ((p1 ∧ (p4 ∨ (True → True))) → p4))) ∨ ((True → (False ∧ ((True ∨ p4) ∨ ((False ∨ False) ∧ (p1 ∨ p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781445455423474982790476388016 : (((p2 ∨ (p4 ∧ ((p3 ∨ (p2 ∨ (((p2 ∨ (False ∨ (False ∨ p1))) → False) → p3))) ∧ (True → (p2 ∨ ((p3 ∨ (p3 ∨ p3)) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192600960969856961078626801133 : (((p5 → ((p1 ∨ False) → ((p4 → p5) ∨ p1))) ∨ p2) → (p2 → (((True ∧ ((((p1 ∨ p3) ∨ True) ∧ p3) → (False ∧ p1))) ∨ p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309360979311322508292157724933 : (p2 ∨ (((((True → p2) ∧ (p1 ∨ p1)) ∧ True) → ((p2 ∧ p4) ∨ (((p1 ∨ p2) ∨ p1) → (p5 ∧ ((False → p2) ∨ p5))))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114143872544153067915991075744 : ((((p4 → (p5 ∧ ((p3 ∨ ((p3 ∨ ((p1 ∧ False) → (p2 ∧ p4))) → (p4 → p2))) ∧ p3))) ∧ p5) → (p4 → (p2 → p3))) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683169119554194534992143651728 : ((((p4 ∧ (False ∧ (True → ((((p5 → (((p2 → False) ∧ p2) ∨ p3)) → p1) ∨ p5) ∧ p2)))) ∧ ((p2 ∧ p5) → ((p1 ∧ False) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64408025916805123532325160234 : ((p1 ∨ (((False ∨ ((True → p5) → p3)) → ((p1 ∧ ((False → (((True → (False ∧ p5)) ∧ False) ∨ p5)) → p4)) ∨ (p2 → True))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165215559013094048298379786607 : ((((((p4 ∨ (p4 → (p1 → False))) ∨ p5) → p3) ∧ (p2 ∨ (p3 ∨ p2))) ∨ (p4 → False)) ∨ (p4 ∨ ((((p2 ∧ p2) ∧ p5) → p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199476250974864532920239782826 : (((p2 ∨ ((p5 ∨ p5) ∨ (p3 ∨ p5))) ∨ p2) → ((((True ∧ p2) → ((p5 ∨ (p3 ∧ (p3 ∨ p3))) → p5)) ∨ True) ∨ ((True ∧ True) ∧ p3))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309705855832716196201153668485 : (p2 ∨ (((p5 ∨ (p5 ∨ True)) → (p3 ∨ (p3 → (p5 ∨ (((((False ∧ False) ∨ p5) ∧ (p2 → False)) ∨ p1) → p2))))) → ((p5 → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686821465124059023616001040778 : ((((p4 ∧ (((p3 ∨ p3) → (((p4 ∧ (p2 ∨ False)) ∨ p4) → (p3 → p1))) ∧ (p4 ∨ p1))) → (((True → (p1 → True)) ∧ p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48462530763014501311147865266 : (((((((p5 ∧ (p5 → ((True ∨ ((p3 ∨ p2) → p5)) → p3))) ∨ (p5 ∨ False)) ∧ (p2 ∨ p5)) → p2) ∧ True) ∧ (p4 ∧ (p3 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217790661378120712399075107237 : (((False ∨ (p3 ∨ False)) → p3) → (p5 → ((p2 ∨ ((p1 ∧ p4) ∨ (p5 ∧ (p1 → p2)))) ∨ (((p1 → True) ∨ False) ∨ (p1 ∨ (p2 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50459887075773760119442607998 : (((p4 ∨ (p1 → (((True ∨ p2) → (p4 ∨ p2)) ∨ (p1 ∧ (((True ∨ (p3 ∧ p2)) ∨ p3) → p4))))) ∨ (((p5 → p1) → False) → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640730304064422475389301397897 : (((((True → True) ∧ ((((False ∨ p1) ∧ (((p1 ∨ p1) ∨ p1) → (((p3 ∨ True) ∧ p5) ∧ (True → False)))) → (False ∧ p3)) → p2)) → p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∨ p1) ∧ (((p1 ∨ p1) ∨ p1) → (((p3 ∨ True) ∧ p5) ∧ (True → False)))) → (False ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : ((p1 ∨ p1) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- False on the left can always be used.
      apply False.elim h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h5.left
    let h16 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h19 : ((p1 ∨ p1) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h20 := h16 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- False on the left can always be used.
      apply False.elim h23
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h24 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156786278937427615043603694939 : (((p1 ∧ ((((p4 ∧ (p3 → True)) → p1) ∧ (p2 ∧ p3)) → (((False ∧ p5) → p5) → p4))) ∧ False) ∨ (True ∧ ((p5 ∨ p2) ∨ (p2 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21397120575011947346576199946 : (((((p1 → p4) → (False ∧ (p5 ∧ (p2 ∧ p1)))) ∧ p3) ∨ (False → (p2 ∧ (True ∨ (p5 → ((True ∨ ((p2 ∨ p5) ∧ p2)) ∧ p4)))))) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319762758716423134387192243550 : (p4 ∨ ((p1 → (((p4 → p1) ∨ p3) → p4)) ∨ (p2 → (((p1 ∨ ((p2 → (((p3 ∨ p1) ∨ (p3 ∨ p4)) ∧ p1)) ∧ p3)) → True) → True)))) := by
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
theorem thm_5_vars_614773329947842637249106702882 : (((((((p4 ∧ p4) ∨ (False ∧ p1)) ∧ ((p5 ∧ True) ∧ (((p4 → p1) → p4) ∧ (False ∨ p1)))) ∨ ((p3 ∧ p1) ∨ (True ∨ p5))) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138014588326138522832936445497 : ((True → (((p3 ∨ ((((((p3 ∧ p1) ∧ p3) → (p5 → p1)) ∧ (p4 ∨ (p4 ∨ p4))) → p4) ∧ p5)) → p2) ∨ False)) ∨ ((p5 ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625662115385135062828349686294 : ((((p1 → ((((p4 ∧ (p2 ∨ False)) ∨ ((p4 → (p4 ∨ p3)) → ((p2 ∧ (p5 → p2)) → p2))) → (p1 → p2)) → (p3 ∧ True))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_165382485672649241187731609786 : (((((p1 ∧ (p3 ∨ p1)) ∧ p2) ∨ ((p5 ∨ (p3 ∨ p2)) → p3)) ∨ ((p4 ∧ p3) → False)) ∨ ((False ∧ p4) → ((p4 → p3) ∨ (p3 ∧ p2)))) := by
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
theorem thm_5_vars_191515074485516726730074136908 : ((False ∧ ((p2 ∧ (p2 → False)) ∨ ((p4 → False) ∧ p3))) ∨ ((((p2 → (p4 ∨ p2)) → p3) ∧ p4) ∨ ((p5 ∨ True) ∨ (p4 ∧ (p5 ∧ p3))))) := by
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
theorem thm_5_vars_657394207722254014645229003442 : (((((p2 → True) ∧ ((((p5 → ((p1 → p2) ∨ p4)) → (p3 → False)) ∨ p2) → ((p2 ∨ ((p5 → p1) ∨ True)) ∨ p2))) ∨ (p3 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_608250657572608837811999334136 : ((((((((((p2 → p5) ∧ p2) → False) → (((False ∧ (p3 ∨ (p5 ∧ p2))) ∧ p5) ∨ (p5 → (p5 ∨ p4)))) ∨ False) ∨ True) ∨ True) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125036815826489017822391621640 : ((((p1 ∨ True) → p2) ∧ (p4 → (p2 ∧ ((p4 ∧ ((((p1 ∨ p5) ∨ (p4 ∨ p4)) ∨ (p3 ∨ True)) ∧ False)) → (p5 ∧ p2))))) → (p2 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65530835487745235520706733016 : ((p3 ∨ (p4 ∨ (((True → (p4 → (((p5 ∨ p1) ∨ (p4 ∨ True)) ∧ (True ∧ (p3 ∧ (p4 ∨ (p1 → p2))))))) ∧ (p2 ∨ False)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321230474881757507102422080898 : (p4 ∨ (p4 ∨ ((((p3 → ((p1 → False) ∧ ((p5 → ((((p1 ∧ True) ∧ p3) ∧ p3) ∧ (False → p5))) ∨ p5))) ∨ (p4 → p2)) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728980509972197290054304971158 : (((((p1 ∨ p5) ∧ p3) → ((p1 ∧ p4) ∨ ((p4 ∨ (((p3 → (p3 ∨ p3)) ∨ ((p2 ∨ (p1 ∨ p3)) → (p5 → p3))) ∨ False)) ∨ p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762362728838818179210188143401 : (((p3 ∧ ((p4 ∧ (True → (((p3 → p3) ∧ (p2 ∨ p5)) ∧ (False ∧ (p5 ∨ ((p2 ∧ False) ∨ (p5 ∧ p5))))))) ∨ (True → (p2 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148280463304663560466660805028 : ((((p4 ∨ (((p3 → p5) → (p2 → ((p2 ∨ True) ∧ (p4 → p5)))) → True)) ∨ p1) → (p2 ∨ (p2 ∧ True))) ∨ ((True → False) → (p3 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64077700152643053294002269935 : ((False ∨ ((p5 ∨ (((p1 ∧ False) → True) ∧ (p1 → (p3 → ((False ∨ p1) ∨ p5))))) ∧ ((True ∨ False) → (True ∧ ((False ∧ p4) ∨ True))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62727825118147245499597137970 : ((p4 ∧ ((((((p1 ∨ (p5 → (((False ∨ p5) ∨ p4) ∧ (p5 ∧ p3)))) ∧ p1) ∨ True) → p5) ∨ (p2 ∨ (p5 ∧ True))) ∧ (p5 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787352873488892961679107478387 : (((p4 ∨ (p3 ∧ (((True ∧ True) → (p5 → (p3 ∨ ((p3 ∧ (((((p1 ∨ p3) ∨ p5) ∧ p3) ∨ p1) → p5)) ∨ p5)))) → (p5 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123190878989454994623815236292 : ((((((p4 → (False → (((True → (p1 ∨ p1)) ∨ p4) ∧ p5))) ∧ (p5 ∧ p3)) ∨ p4) ∧ p1) ∧ (((p5 → p3) → p4) → p4)) → (p5 ∨ True)) := by
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
    let h9 := h8.left
    let h10 := h8.right
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
theorem thm_5_vars_133839213733258507959639176715 : ((((p1 → False) → ((p3 ∧ p3) ∧ (False ∨ (((p4 ∧ p3) ∧ p4) ∨ (p4 ∨ ((p4 ∧ p4) ∧ (p5 ∨ False))))))) ∧ True) ∨ (True ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769096967557692578015793661716 : (((p5 ∧ ((True ∧ p1) ∧ (((p1 → (p5 ∧ (False → p5))) ∨ p4) ∧ ((p4 ∧ ((p3 → (p1 ∧ p1)) ∧ p4)) ∧ (True → (p1 ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138177357070490221453675858277 : ((p1 → (((False → (p2 → p1)) ∨ p2) → ((p4 ∧ (True → (p5 ∨ ((True ∧ p5) → p5)))) → ((p3 ∧ p4) ∨ p2)))) ∨ (p3 ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49035490070442356491357482515 : ((((p1 ∧ (((p2 → (False ∧ ((p1 → p5) ∨ (True ∧ (((False ∧ True) → p5) → p2))))) ∨ False) ∨ p5)) → False) ∨ (p2 ∨ (p5 → p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60216456319386952271077441667 : (((True → p1) → (((((p1 → (((p3 ∧ False) ∨ p3) → (p3 ∨ p3))) → True) ∨ (p4 ∨ p3)) → ((p4 ∨ p5) → (p3 → p1))) ∨ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h12 := h1 h11
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h15 := h1 h14
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h17 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h22
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h26 := h1 h25
        -- One of the premise coincides with the conclusion.
        exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111625142699563458075505711681 : (((((p5 ∧ (p2 ∧ ((p2 ∨ p2) ∨ ((p3 → (False ∨ ((p5 → (True ∨ p4)) ∧ p1))) ∧ p5)))) ∨ (p5 ∧ False)) ∨ True) ∨ p5) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54152189692735641535801455565 : (((p2 → (((p3 ∧ (p4 → p5)) ∨ p2) ∧ (p4 ∨ p4))) → (((False ∨ ((False ∨ ((p5 ∨ (p4 → p5)) → p1)) ∧ p4)) ∨ True) ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_711886846701592538878505195963 : (((((p2 ∨ ((p4 → False) ∨ p2)) ∧ p1) ∨ ((p4 → (((p2 ∨ (p3 ∧ p3)) → True) → (True ∨ (p1 ∧ (p3 ∨ p1))))) → (p5 ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258565654033226254784852467069 : ((p5 ∨ p3) → (p2 ∨ ((((p3 ∨ (((p4 → (p3 → (((True ∨ (p2 ∧ p1)) → (False ∧ p5)) ∨ p5))) → p4) → p3)) ∧ False) ∧ False) ∨ True))) := by
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



