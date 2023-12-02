variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82384048410949131594413986276 : (((((p2 → p1) → (p4 ∨ p3)) ∧ (((((p1 ∧ (False ∧ (False → False))) ∨ p3) ∧ p5) ∨ True) → p3)) ∧ (((p2 ∨ p1) ∨ True) → False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∨ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178304631624703662495057847630 : (((((p3 ∨ ((p5 ∨ p2) ∧ p5)) ∨ (p4 → p4)) ∧ p3) ∨ (p3 ∨ True)) ∨ (p1 ∨ (((p3 ∧ ((p2 ∨ p5) → p2)) → p4) → (p5 → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113664851825805552131878835115 : ((((((p4 ∧ (p3 → ((((p5 ∧ (((True ∨ p1) ∨ p5) ∧ p2)) ∧ True) → True) → p3))) ∨ True) → False) ∨ p1) → (p3 ∨ p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324454472339807232756249632937 : (p5 ∨ ((True ∧ ((p3 → True) ∨ False)) ∧ (((True → p2) ∧ (False → True)) ∨ (p4 ∨ ((p1 → p3) → (((p5 ∧ p4) ∨ False) ∨ (p1 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175498309056285308775768446120 : ((p3 → ((False ∧ (((((p2 ∨ p5) ∧ p4) ∨ False) → True) ∧ p1)) → (p4 ∨ p3))) → ((True → p3) ∨ (p4 → (p4 ∨ ((p3 ∨ p2) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688964720718274604624154404011 : (((((((((True → p4) ∨ p3) ∨ (p1 → ((p4 ∨ False) → p5))) ∧ p2) ∧ p4) ∨ p5) ∨ (((p5 → False) ∧ (False → p1)) ∨ (p3 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147646737861862458324157272465 : ((((p2 → (((True → (p3 ∨ ((p1 → p1) ∧ p5))) ∨ (p3 ∧ (p5 ∧ (p1 ∨ p5)))) ∨ p2)) → p5) → p1) ∨ (((p2 ∨ p5) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301796383919788974918072289162 : (False ∨ ((p4 ∧ True) ∨ (p4 ∨ ((True → (((True ∨ p5) → True) ∧ ((True ∧ (p5 ∨ (p2 ∨ p4))) ∨ ((p2 → (True ∨ p2)) ∨ p4)))) ∨ p5)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148480398206815869288374623752 : ((((p5 ∨ (((p1 ∨ p3) ∧ p3) ∨ ((True ∧ False) → p1))) ∧ p5) ∨ (p1 ∨ (True ∨ ((p5 → p1) ∨ False)))) ∨ ((p2 ∨ (p2 → True)) ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263079207119075118834693247057 : (True ∧ ((((((p1 ∧ ((p2 ∨ (p2 ∨ (p3 → p2))) ∨ (((p2 ∨ False) → p3) ∧ p3))) ∨ False) ∨ p3) ∧ (True ∨ p4)) ∨ p5) ∨ (p3 → True))) := by
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
theorem thm_5_vars_112900543261500617450069694679 : ((((p5 → p5) ∧ ((p5 ∧ False) → ((False ∧ (((p4 ∨ ((True ∧ p3) ∨ p3)) ∨ p4) ∧ (p4 ∨ p3))) ∧ (True ∧ p4)))) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57688535663082497332609713123 : ((((p5 → False) ∨ False) → ((p2 ∨ (((p3 ∨ p5) ∧ ((p2 ∧ ((p5 → ((p2 → p1) → p4)) ∨ p1)) → (p3 → p5))) ∧ p2)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_579635070568093250532257961049 : (((p4 → (((((True ∧ (((p4 → (p3 ∧ (p2 ∨ (p2 ∨ (((p1 → p1) ∧ p5) ∨ p2))))) → False) ∨ p2)) ∨ p4) ∧ p2) ∨ False) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218894379797539733439772080473 : ((p3 ∧ ((True → False) ∧ p5)) → ((False ∨ (p2 ∨ ((p4 ∨ ((True → p1) ∧ p5)) → (p1 → ((False ∨ p4) ∨ ((True ∨ p2) → p3)))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56571414211898032018772656448 : (((True → (p1 ∧ (True → p1))) → (((p5 ∨ ((p2 ∧ p4) → (p5 ∧ p3))) ∨ (((p5 → True) ∧ False) → ((p3 ∨ p4) → p3))) ∨ p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198742290198445786684424655117 : ((True → ((p3 → (p4 → (False ∧ False))) ∧ p5)) ∨ (p2 ∨ (p3 → (p1 → (((p1 ∧ p2) ∧ (((True ∧ p2) ∧ (p5 → True)) ∧ False)) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351566471895293719012868454141 : (p4 → ((((p5 → (((p1 ∨ p2) ∨ False) ∨ (p5 ∧ (p3 → True)))) ∧ p1) ∧ ((p1 ∧ False) ∨ p5)) → ((p3 ∨ (p2 → (p3 ∧ p4))) ∨ p4))) := by
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
  cases h4
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679884505742172009918534973259 : (((((((True → p3) → (((p4 ∧ ((p4 ∧ p1) ∧ (p4 → p3))) → (False ∨ p1)) ∧ p4)) ∧ p2) → True) → ((p5 → (p2 ∨ p2)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52139323493303700821402984189 : (((((p5 → (p4 → p2)) ∧ ((True ∨ (p2 ∧ (True ∨ True))) ∨ p5)) ∨ (p4 ∨ p4)) → ((p3 ∨ (p4 ∧ p3)) → ((True → p5) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694679516867054018515127618447 : ((((p1 ∨ ((((False ∧ False) ∨ ((p3 → p1) → (False ∧ p1))) ∧ False) ∨ p5)) ∨ ((((False ∨ p5) → True) ∧ ((p4 → True) ∨ True)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53525192860619352907421660413 : (((p3 → ((((p5 ∧ p2) ∨ (p2 ∨ p5)) ∨ (p4 ∨ True)) ∨ p3)) → (((((p4 ∧ p3) ∧ p4) ∧ ((p5 ∧ False) ∨ p3)) ∨ p3) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677298418344643187509950431689 : ((((((p2 → p4) → (((p5 → (p1 ∨ (((p2 ∨ (p5 ∨ p5)) → p5) ∨ p2))) ∧ p3) ∨ p1)) ∧ p1) ∨ (((True ∨ p2) ∧ p2) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_218066003089975533193686775328 : (((p4 ∨ p2) ∧ (p5 ∨ False)) → ((((p1 → p4) → p1) ∧ ((True ∨ (True → False)) ∧ ((((p2 → False) ∨ p3) → True) → (p1 → True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190960380550342026632308157652 : (((p5 ∨ ((p2 ∧ p4) ∧ True)) ∧ (True ∧ (p3 ∧ p5))) ∨ ((p1 → p1) → (((((p4 → p2) → p5) ∧ p3) ∧ ((p2 ∨ p3) ∨ p1)) → p3))) := by
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
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174731492122216273838006416185 : ((((p4 → p4) ∨ False) → (p3 ∨ (p1 → ((True → p3) ∨ ((p3 ∧ p3) → p2))))) → (((False ∨ ((p3 ∧ p1) ∧ (p4 ∨ p2))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615242370962228690418740804410 : (((((p2 ∨ ((p3 ∧ False) ∧ ((p4 → (p4 ∧ True)) ∧ ((p1 ∨ p4) ∧ (p5 ∧ p1))))) ∧ ((((p5 ∨ p3) ∧ True) ∨ p3) → p5)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_137779458900674420792446762612 : ((p2 ∨ ((False ∨ ((p5 ∨ p4) ∨ p4)) ∧ (p2 → ((True ∨ p5) → (((p1 ∧ (p3 ∨ True)) ∧ p1) ∨ (p4 → p5)))))) ∨ (p1 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50245681594532226764232405309 : (((((((p1 ∨ p5) → p1) → (False → (p3 ∨ p5))) ∧ ((p4 ∨ ((p5 ∨ p3) ∨ p4)) → p1)) → p4) ∨ (((False ∨ True) → p5) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111220655988777219396326434997 : ((((p3 ∧ (True ∨ p4)) → ((p5 → p4) ∨ (((p3 → (((False ∨ p3) → (p5 ∨ p2)) ∧ (p3 ∧ p5))) ∨ p3) → p4))) ∧ p4) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3270806444438944029972158244 : ((p2 → p1) ∨ ((p3 ∧ (True → False)) → (((p1 ∧ p3) ∧ ((p5 → (p3 ∨ True)) → (p5 ∨ p4))) ∨ (p2 ∧ (p5 → (p2 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61211835813631355198566253929 : ((False ∧ ((p5 → p2) → ((((((p4 ∧ p2) ∧ ((False → (p5 ∨ False)) → p2)) ∧ (p1 → p3)) ∧ p3) ∨ ((True ∨ p5) ∨ p1)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58992166088042602519306162226 : (((p3 ∧ False) ∨ (((p4 ∨ ((True ∨ (False ∧ p5)) ∧ p2)) ∧ ((((p5 ∧ p3) ∧ p5) ∧ False) ∧ p2)) ∧ ((True ∨ (True ∨ p5)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111526554633562042509008069703 : (((((((p1 ∨ True) → (True → p1)) ∨ ((False → p1) ∧ ((p5 ∨ (p1 ∨ False)) → (p3 ∧ (p2 ∧ False))))) ∧ False) ∧ p4) ∨ True) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40800043914800526903980142063 : ((((True ∨ (p3 ∨ (((((True ∨ p3) ∧ p2) → (p5 ∨ (True ∨ p3))) → p5) ∧ (((p2 → True) → (p2 → p3)) → p3)))) → p5) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183752448714037644845238813804 : ((p5 → (((p1 → p4) ∧ (p2 ∨ p2)) → (p2 ∧ (p1 → p2)))) ∧ ((((p4 ∨ p2) → False) ∨ ((p5 ∨ (p4 ∧ p3)) ∨ False)) ∨ (p2 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147860307450186405523899271381 : (((p1 → ((((((p4 ∨ p3) ∧ (False ∧ (p1 ∨ p2))) ∧ (p1 ∧ True)) → True) ∧ (p2 → p1)) ∨ False)) → p3) ∨ (True → (False → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171967612864047654936375133421 : (((False ∧ (p4 ∧ (((False ∧ p4) ∨ (p3 ∧ (p1 → p2))) ∨ p2))) ∧ (p4 ∨ p3)) ∨ ((p3 → ((p1 → p5) ∨ p4)) → (True → (True ∨ p2)))) := by
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
theorem thm_5_vars_99114306415676413613097468596 : ((True → (p1 ∧ ((p5 ∧ ((p5 ∨ True) ∧ p2)) ∧ (False ∧ (p4 ∨ (p3 ∨ ((p3 ∧ (p4 ∨ p5)) ∧ (True ∨ (p1 ∨ (p4 ∧ True)))))))))) → p4) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113799381759598480657647146344 : ((((p2 ∧ p2) → (((p2 ∧ (p1 ∨ True)) → (p2 ∧ ((p3 ∧ p3) ∨ p5))) ∧ (p2 → (p3 ∨ (p3 → p4))))) → (p4 ∧ p3)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39750772968010013763708693531 : (((True → (((p2 ∧ (((True ∧ ((p2 ∨ (p3 ∨ True)) ∨ p2)) ∧ True) ∨ (((False ∧ p3) ∨ p2) → (p3 → p1)))) → p4) ∨ p2)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147606234413223022879770745174 : (((((False → p3) ∧ (((((p2 → (False → p4)) → (p5 ∧ p1)) ∧ p3) → (p2 ∧ False)) → p3)) ∨ True) → False) ∨ (True ∨ ((True → p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684711125312464577494113260517 : (((((p3 ∧ p2) ∧ ((p4 ∧ True) → (((True → (False ∨ False)) ∨ p2) ∧ ((False → True) ∨ True)))) ∨ ((False ∨ p2) ∨ ((True ∧ True) ∨ p3))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_114395938553397085408527935211 : (((((((p5 ∨ (False ∧ False)) ∧ (p4 ∧ p2)) ∨ False) → p1) ∧ ((p3 ∨ p2) → (p1 ∨ p5))) ∨ ((p4 → p3) ∧ (p2 ∧ p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134302562845318569663096777125 : ((((p1 → p5) → (p5 → ((((p1 ∨ p3) ∨ (((False ∨ p1) ∨ (True ∨ (p2 ∨ p1))) → p5)) → p1) ∨ True))) ∨ p2) ∨ ((p3 → True) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304730935641714464554176809941 : (p1 ∨ (((p5 ∨ (((p4 → ((p5 ∧ p3) → p5)) → p5) → False)) ∧ (p4 ∧ (p2 ∨ ((p5 ∨ (p1 ∧ (p1 ∨ True))) → False)))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781062381340473932068434473779 : (((p2 ∨ ((p2 → p1) ∧ (((p3 → p5) ∧ (((False → True) → p4) ∨ ((p2 → False) ∨ (p2 ∨ p3)))) ∧ (((p5 ∧ p3) ∨ p4) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615819564011607708519769387098 : ((((((True ∧ ((p3 → True) ∧ ((False ∧ ((p1 ∧ p5) ∧ p2)) → p5))) → p3) ∨ (((True ∧ (p2 → (p2 ∨ p5))) ∨ p4) ∨ True)) ∨ p4) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17226276581598362161196255558 : ((((True ∧ ((p4 → (p2 ∧ (p2 ∧ ((p2 → p1) ∨ p1)))) ∧ True)) ∧ (((p2 ∧ p4) ∨ p2) ∨ (p1 ∧ p3))) → (p1 → (p1 ∧ p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h27 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- One of the premise coincides with the conclusion.
    exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186668207895467102310492972118 : ((((p1 → (True ∧ p3)) → (p3 ∨ p1)) ∧ ((p2 ∧ p5) ∧ p3)) → (((((p5 ∨ (p3 ∨ (False ∧ p1))) ∨ p5) → (p5 ∧ p1)) ∨ p3) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113503968016225396184760383443 : ((((p1 ∧ (p4 ∧ (((p3 → (p1 → p1)) ∧ True) ∨ (p2 ∨ (p5 → p4))))) ∧ ((p5 → p1) ∨ (p2 ∧ p5))) ∨ (True ∨ True)) ∨ (p3 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114456091024387790361430481078 : ((((p2 ∧ ((p5 → (((p3 ∨ (p5 ∧ (False → True))) ∧ p4) ∨ (False → False))) ∨ p2)) ∧ True) → (((p3 ∨ p1) → p5) ∧ p1)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168855923711742307152633426815 : ((p3 ∨ (p1 → ((p4 ∧ p5) → ((True ∧ ((p5 ∨ False) → (True ∧ True))) ∨ (False ∧ True))))) → (((True ∧ p2) ∧ False) ∨ (False ∨ (p5 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144696277603934794545607316479 : ((((((p4 → p3) → ((False ∧ (p1 → (p4 ∨ p5))) ∧ (p2 ∧ p1))) ∧ False) ∨ True) ∧ (p1 → (p1 → p1))) ∧ (((False ∧ True) ∧ False) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322326517097155732489084289393 : (p5 ∨ (((((((((p4 ∨ p3) ∧ (True ∧ p1)) ∨ ((p1 ∨ (p3 → p2)) ∧ (p2 ∨ False))) → True) → p5) ∧ p2) ∨ p5) ∨ (False ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61968165917579702532508896391 : ((p2 ∧ (((p2 → (((False ∧ p3) ∨ False) ∧ (False ∧ p2))) ∧ p2) ∧ ((((p5 ∧ p3) ∧ p1) ∨ ((p1 ∨ p2) ∧ p4)) ∧ (p3 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112135809076579268299437420353 : (((False ∧ ((p4 ∨ p1) ∧ (True ∧ ((True ∧ (((p4 → (p1 ∨ p3)) ∧ (False ∧ True)) → (p3 → (p2 ∨ p2)))) → p3)))) ∨ True) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111863830093479404137049521555 : ((((p5 ∧ (((p2 ∨ (p2 ∧ (p2 → (p3 → (p1 → p3))))) ∧ (p3 → p2)) → p4)) ∧ (False ∨ ((p4 → p2) ∧ True))) ∨ True) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149897357927562314433919170364 : ((p2 ∨ (False ∨ (((True → (True ∧ p2)) → (((p2 → (False ∨ p5)) → p4) ∨ False)) ∨ ((p3 ∨ False) ∧ p1)))) ∨ (p3 → (p5 → (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159692346855752138888264411789 : (((((p4 → (p3 ∧ (False ∧ (p2 ∨ (((p3 → True) → True) ∧ True))))) ∨ p2) → (False ∧ p4)) ∨ True) → ((p4 ∨ p3) → ((p3 → False) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208907163524554501675416654896 : ((p5 ∧ ((p3 → (p4 ∧ False)) ∨ p4)) → (p2 ∨ ((((True ∨ (p4 ∨ ((p5 ∧ p5) ∨ (True → p4)))) ∧ (False ∧ p4)) ∨ p5) ∨ (True ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190312891278058220008569841319 : (((((p1 ∧ p5) ∨ (p3 ∧ p2)) ∧ (p2 → p1)) ∨ True) ∨ ((((((p3 ∨ False) ∨ False) ∧ p5) → p4) → ((p2 ∧ (False → p3)) ∧ p1)) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326012556027225068905026754743 : (p5 ∨ (True → ((True → p2) → (((p1 ∨ p3) ∨ (p1 → False)) ∨ ((False → (((True ∨ (False → p5)) → True) → False)) ∧ (p4 → (False ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342602421672313280026608964386 : (p2 → ((((p5 ∨ p3) ∧ ((p2 ∨ False) ∨ p3)) ∨ ((p4 → p3) → p4)) → ((True ∨ p5) ∧ ((p5 ∨ p1) ∨ (True ∨ ((p3 ∨ p5) ∨ p5)))))) := by
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
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h23 =>
          -- False on the left can always be used.
          apply False.elim h23
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h30 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112127306809316404388100895432 : (((True ∧ (p4 ∨ ((True ∧ (((p3 ∨ p1) ∧ True) ∧ (p5 ∧ ((p2 ∧ (p1 ∧ (p1 ∨ p3))) ∨ (p4 ∧ True))))) ∨ p3))) ∨ True) ∨ (p2 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44223788249567891244718800306 : (((((((((((True ∨ (p4 ∨ p5)) → p4) ∧ True) ∧ False) → (p1 ∨ p2)) ∨ p5) ∨ False) → p3) ∨ (p4 ∧ ((p2 ∨ p4) → True))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46541521318931770044849276201 : ((((p1 → False) ∨ (((p4 → ((((p5 → ((p3 ∨ (p2 ∧ p4)) → (False ∧ p2))) → p5) → p3) ∨ p2)) ∨ p2) → p1)) ∧ (p5 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47783655779620539378069373834 : ((((((((False ∧ p5) ∨ (False ∨ p3)) ∨ ((p4 ∧ (p2 → p1)) ∧ (p3 ∧ p5))) → ((False ∧ p5) ∧ p4)) ∧ p5) → p3) → (p5 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157289585223858254489019092794 : ((((p2 ∨ p4) ∨ (((((p3 → ((p1 ∧ p4) → False)) ∧ p5) ∧ (p1 ∨ True)) ∧ True) ∨ p2)) → p1) ∨ ((((p2 ∧ False) ∨ p4) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225037797199659328447570378729 : (((False ∧ p3) ∧ p5) ∨ ((p4 ∧ ((p5 ∧ False) ∧ True)) ∨ (False → (((((False ∨ p2) ∨ p1) ∧ p4) → (False ∧ False)) ∧ (p1 → (True → False)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768984030851013741181739451662 : (((p5 ∧ (((p5 ∨ p2) → p2) ∧ ((True → p1) ∨ (((False ∨ (((p2 ∨ p2) ∨ p2) ∨ p2)) ∨ (((False → False) ∨ p2) ∨ p2)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588892418593096845955242530631 : (((((p3 ∨ ((p3 → ((p4 ∧ ((False → p2) → p1)) → ((True ∧ (p3 ∧ (p1 ∧ p1))) ∨ (p5 ∨ (p5 ∨ p5))))) → p5)) ∨ p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178032675498028767505226911099 : (((p5 → (((p2 → p3) → p3) ∧ (p5 ∨ (p3 ∧ (p3 ∧ p4))))) ∨ p1) ∨ ((p1 ∧ p3) → ((((p1 ∧ False) → p3) → (p4 ∧ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161155877193594885624354641386 : (((False ∧ p4) ∨ (((p4 ∨ (p3 ∨ False)) ∨ ((p3 ∧ p5) ∧ p3)) → ((True → (True ∧ p4)) ∨ p4))) → ((((True ∨ p4) → p4) ∧ p3) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46213922519090212951582778162 : (((((p2 ∧ ((((((p1 ∨ p1) ∧ p2) ∨ p3) → p5) ∨ p4) → p4)) ∧ ((p1 → True) ∧ (p1 → p4))) ∧ (True → p1)) ∧ (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64857732756306797599529680933 : ((p2 ∨ ((p3 ∧ ((True ∨ ((p4 ∧ (p2 ∨ p3)) ∨ p5)) → (p1 ∧ (((((False ∧ p1) ∨ p3) → p1) → p4) → p3)))) ∧ (p2 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231972543216721469054681330503 : (((p1 ∨ p5) → False) → ((((p2 → (((False → (((p5 ∧ p3) ∨ p4) ∨ p4)) ∨ (p1 ∨ p2)) → p3)) ∨ p1) ∧ p3) ∨ (False → (p3 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709277671091525075586382516446 : (((((p2 → p1) ∨ (False → (True → (p4 → True)))) → ((((p2 → (p4 ∨ False)) ∧ p2) ∨ (p3 ∨ (False ∨ False))) → (p4 → (p4 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58852563216337632714444480785 : (((True ∧ p3) ∨ ((p5 ∨ ((p5 → False) ∧ False)) ∨ ((((((p1 ∨ True) ∧ p2) ∨ False) ∧ p3) ∧ p3) → ((p3 → True) → (p2 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173429347526933540822656094839 : ((p5 → (False ∨ (p2 ∨ ((True → ((p3 → p1) ∨ ((p3 ∧ p3) ∧ True))) → p2)))) ∨ ((((p5 ∧ (p3 ∧ p3)) ∧ p2) ∨ p3) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84578602225092705575591148490 : ((((p3 ∧ p2) → ((True → True) ∧ (p4 → (((True → (p1 → p5)) ∨ p3) ∨ p2)))) → ((p1 ∧ p4) ∧ (((p3 ∨ False) ∨ p5) ∧ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ p2) → ((True → True) ∧ (p4 → (((True → (p1 → p5)) ∨ p3) ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329715014028468565633914784013 : (True → ((p1 → False) → ((p4 → ((((((False ∧ (p4 ∧ p5)) ∨ p4) ∨ (p4 → (p2 ∨ p4))) → False) → p4) → False)) ∨ ((False ∨ p1) → True)))) := by
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
theorem thm_5_vars_356557867157780047214584999692 : (p5 → ((((p1 ∧ (p1 → (p2 ∧ p1))) → True) ∧ (True → True)) → (((p1 ∨ (True → (((p2 → True) ∨ False) → p4))) ∨ (p4 → True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191678692083314228763807058502 : ((p5 ∧ ((False → (p1 → p4)) → ((p1 ∧ p5) ∨ p5))) ∨ ((p2 → (((p1 → p2) ∧ (True ∨ p1)) → (p1 ∧ p3))) ∨ ((p5 ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150079870556844365617355551509 : ((True → (False ∧ (((((p5 ∧ p1) ∧ True) ∧ p5) → p4) → ((((p3 ∧ p1) ∨ False) ∧ (False ∧ p4)) ∧ p1)))) ∨ (False → ((False ∧ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54572820400195869052687914865 : (((False ∨ ((p4 → (p1 ∨ p1)) ∧ (p1 ∨ p3))) ∨ ((p3 → False) → ((p1 ∨ (p4 → (p4 ∨ p1))) ∨ (((p3 ∨ p3) ∨ p5) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320137343466541945982911118880 : (p4 ∨ ((p3 → (p4 ∧ p1)) → ((p3 → p1) → (((p2 ∧ p2) ∨ p2) → ((((p1 → (False ∧ p3)) ∧ True) ∨ p4) ∨ (True ∨ (p4 ∧ p5))))))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615894177311420182748697161947 : (((((p2 ∧ ((p2 → (False ∨ (p4 → ((False ∨ p1) → p1)))) → (p5 ∨ True))) ∨ (p2 → (((p5 → True) ∧ False) ∨ (p5 ∨ p1)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740915292273457211442636462568 : ((((p3 ∨ p2) ∨ ((p5 → ((p3 ∨ p4) ∨ ((((True ∧ (p2 ∧ ((p2 ∨ p2) ∨ False))) ∧ p3) ∨ p5) → p3))) ∨ (False → (p3 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57434773679699139325764158981 : (((p3 ∨ (True → p3)) ∨ ((((False ∧ p2) ∨ p3) ∧ (True ∨ p3)) → ((((((p3 ∨ p4) → p1) ∧ (False ∨ p5)) → p3) → p4) ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
theorem thm_5_vars_186940537949171038790238897059 : (((p2 → (p5 → p5)) ∧ (True → ((p1 → p3) ∧ (p2 ∧ p5)))) → (((p2 → (False ∨ True)) → p5) ∨ ((p1 → p2) ∧ ((p5 → p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64162126606026457923197330145 : ((False ∨ ((p5 ∨ p5) ∧ (((False → p3) ∨ False) ∧ (p2 → ((((p2 → False) → False) ∨ True) → (p2 ∧ (p3 → ((True → p1) → p3)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68184792437887246850192842219 : ((p3 → ((((((p1 ∧ p1) ∨ (p2 → (p5 → (False → (p5 ∧ (p3 → False)))))) → p1) ∨ ((True ∨ p4) ∧ p2)) → (p3 ∧ p4)) ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133602262754923174715174919310 : (((((((((((p3 ∧ False) → (p5 ∨ p2)) → p2) → (p4 ∨ p1)) ∨ p4) ∨ (p5 → p2)) → p4) ∨ p4) → p1) ∧ False) ∨ ((p3 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137063500414535397900672765922 : (((p3 → False) → (((p2 ∨ p2) → ((True → (True ∨ (p5 ∧ p3))) ∨ True)) → (p1 ∨ (p2 ∧ ((p3 ∨ True) → p2))))) ∨ ((p5 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254230179664283141314747237531 : ((p2 ∧ p2) → (((False → ((((p3 ∧ (p3 ∧ p3)) ∨ (p1 ∨ p3)) ∧ p1) ∧ p3)) → p1) ∨ ((True → p5) ∨ ((p4 → (p5 → p3)) → p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149479450613957773489623347742 : ((False ∧ (p4 ∨ (((False ∨ p3) ∨ (((p4 ∨ (p1 → p3)) ∨ False) ∨ p1)) → (p5 → (p1 ∧ (True ∨ p1)))))) ∨ (p2 → ((False → True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219558834093592711992420514986 : ((True → ((p5 → p1) ∧ False)) → ((p4 ∨ p3) ∧ (((((True ∧ (p1 ∧ p5)) ∨ (p1 ∨ (p4 ∧ p5))) → (p5 ∨ p1)) ∧ (False → p5)) ∨ p1))) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585395774416332051556099748130 : (((((((p5 ∧ (p4 ∨ p3)) ∨ (((p2 ∨ True) ∧ p2) ∧ (False ∧ ((p2 → ((p4 ∨ (p2 → True)) ∨ p1)) ∧ False)))) ∧ p2) ∧ p2) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777427545279772628569872222070 : (((p1 ∨ ((((p3 ∨ p5) ∨ p1) ∨ ((True ∧ (p4 ∧ ((p4 ∨ (p4 ∨ True)) ∨ p4))) → False)) ∨ ((p2 ∧ ((p3 → True) ∨ p2)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219949198307078554903654925825 : ((p5 → ((False ∨ True) ∧ p4)) → (False ∨ ((p4 ∧ p3) ∨ ((p3 ∨ ((p2 ∧ (p3 ∧ False)) ∨ ((p1 ∧ p2) → ((p4 → p2) → p2)))) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



