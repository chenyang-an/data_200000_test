variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193567543152134770669821474347 : (((p1 ∨ p3) → ((True ∧ (p1 → p4)) ∧ (p4 ∧ False))) → (p2 ∨ ((((p1 ∨ p5) ∧ (p3 → (p4 ∨ (p2 → p4)))) → (p5 → p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240847125689845157086094405096 : ((True → True) ∧ (((((p1 ∧ (((False → p1) → p3) ∧ p3)) ∨ (p1 ∨ (p2 ∨ (p1 → (p4 → (True ∨ p2)))))) ∧ (p5 ∧ p4)) ∧ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40984547177398481929917384643 : ((((p2 ∧ ((p3 ∧ p4) ∧ (p5 ∨ (p2 → (((p3 ∨ p2) → (True ∨ (((p4 ∨ p4) → p2) ∧ False))) → p5))))) ∨ (p1 ∨ p1)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226358380399364449671821535022 : (((True → False) ∨ p4) ∨ (((False ∧ (p1 → False)) ∧ ((p2 ∧ p5) ∨ p5)) ∨ ((False → p1) ∧ ((False ∧ (((p1 ∨ p2) → p5) ∨ True)) → p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120874589497279974813706441675 : ((((((p3 → p4) ∧ ((p4 ∧ p1) → p2)) → False) ∧ (p3 → ((((((p4 ∧ p3) ∨ p3) → p1) → p3) ∧ p5) → p3))) ∨ p5) → (p4 ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113768895057385928059761778280 : ((((p2 ∧ (p4 ∨ (p5 ∧ True))) ∧ (((p1 ∧ ((p2 ∨ p2) ∧ p4)) ∨ p3) ∧ ((p3 ∧ p1) ∨ (p2 ∨ False)))) → (p5 ∨ p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721463435042121432431485500401 : ((((p2 ∧ ((p4 ∨ p2) ∧ True)) → ((p1 ∧ True) ∨ (((p1 ∧ p2) ∨ p1) ∧ (((p4 ∧ (True ∧ p4)) ∧ True) → (True ∧ (True ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164602611076575077405865250258 : (((True ∧ (((p3 ∨ p5) ∧ (p4 ∨ p4)) ∨ (((p5 ∨ (p5 ∧ False)) ∨ p3) ∧ True))) ∧ p5) ∨ (((p4 → (True ∨ True)) ∨ p1) ∨ (p5 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178494513734480637669266859862 : ((((p2 → p3) → (p2 ∧ (p3 ∨ (p5 ∨ p2)))) ∨ (p4 → (p3 ∨ p5))) ∨ (((False → p3) ∨ p1) ∧ ((True ∧ ((p4 → False) ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41845710601513100187894322244 : ((((True → (p1 → p1)) ∧ (((p2 ∨ p1) → ((p4 → ((p3 ∧ p1) → (True ∨ p3))) → (((True ∨ True) → p1) ∧ p1))) ∧ p3)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190194432156956250287048955543 : (((p2 ∨ ((False → ((p2 ∨ p5) ∧ False)) → p2)) ∧ p5) ∨ ((False → ((False → p4) ∨ p4)) ∨ (False → (False ∨ ((p5 ∧ (p3 ∧ p1)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45816779035166807065061376174 : (((p2 → (((((p1 → ((p2 ∧ (p3 ∧ p3)) ∧ ((((p5 ∨ p4) ∧ p3) ∨ p2) ∨ p2))) → False) ∧ p3) ∧ (p5 ∨ p1)) ∧ p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147364466129042097373062104918 : (((((((((p3 → p3) → p5) ∧ p4) ∧ p5) → (p1 → p2)) ∧ p2) ∧ (((p1 ∨ p3) ∨ p4) ∨ p4)) ∨ p3) ∨ (p2 ∨ (p4 → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135757137533607809984864117463 : (((p4 ∧ (p4 ∨ (p3 ∨ (p2 ∧ (p4 ∧ (True ∧ (False ∨ (p1 ∨ True)))))))) ∨ (p3 ∨ (((False → p1) ∨ p1) ∨ p3))) ∨ ((p1 ∨ p3) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303911315058242835323221959087 : (p1 ∨ ((((p2 → (p3 ∧ (p2 ∧ (p1 ∧ (p1 ∧ (p5 ∧ p5)))))) ∨ p5) ∨ ((True ∨ p4) → (((p5 ∧ p3) → (p2 ∨ True)) ∨ p1))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186026484300506667047388201204 : ((((((p4 ∨ ((p3 ∨ p4) ∧ p2)) → True) ∧ p1) ∧ p2) ∨ False) → (((p5 → p2) ∧ ((True ∨ (p3 ∨ p1)) → (p3 → (False ∨ p5)))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337142359181734692233461319476 : (p1 → ((True → (p2 → ((((False ∨ p4) ∨ p5) ∨ p3) ∨ (False ∨ (p1 ∧ ((p2 → ((p2 ∨ p3) ∧ p1)) ∨ (p1 ∧ True))))))) ∨ (p2 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208862475160982751417289430963 : ((p4 ∧ (((p3 ∨ p5) ∨ True) → False)) → ((p3 → ((((p4 ∨ p5) ∧ (p5 ∨ ((True ∧ (False ∧ p5)) ∧ p2))) ∧ (p3 ∨ p3)) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112867822781630287791467506270 : (((((False → True) ∧ p5) → ((((((p3 ∧ p1) → False) → (True ∨ p1)) → p5) ∧ p3) ∧ ((p3 → (p5 ∨ p2)) → p3))) → p1) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134930587063508288865540803039 : (((((((p1 ∨ p1) ∨ False) ∨ p2) → ((((p5 → p3) → p4) → (p5 ∨ (p4 → p1))) → p1)) → p4) ∧ (p1 ∧ False)) ∨ ((False → False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346900846470977646713379423939 : (p3 → ((((((True ∨ p2) ∧ p2) ∨ ((p3 → p5) → p5)) ∨ (((p5 → True) → p4) ∨ p1)) → p1) ∨ (((p5 → (p5 ∨ p2)) ∧ True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686818686311175330018923082588 : ((((p4 ∧ (((True ∨ (p4 ∧ ((p2 → ((p1 → True) → (False ∨ False))) ∧ True))) ∧ p1) → p1)) → (((p5 → p3) ∧ p3) ∨ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161132944710661831556024492400 : (((p1 → p1) ∧ (p3 → ((((p4 ∨ p5) ∨ p3) ∨ (((p1 ∨ p5) → p4) ∨ p4)) ∧ (p5 ∧ p3)))) → ((True → False) → ((p5 ∨ p5) → p3))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_467376103110678202316008499044 : (((((((p1 → (((True ∧ p4) ∧ p1) → True)) ∧ p4) ∨ p1) ∧ (p1 ∨ p2)) ∨ (((p4 → False) ∨ (((p4 ∨ p1) ∧ p5) ∨ True)) ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259373977669082162749268247065 : ((False → p3) → ((p4 ∧ (((True → p2) ∧ (False → (p3 ∨ ((p1 → (p5 ∧ (p4 ∨ p2))) ∨ (p2 → p3))))) → (p5 ∨ (p4 → True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116107416093126489936205567462 : ((((True ∨ True) → False) ∧ ((p3 ∧ (p5 ∧ ((p5 ∨ (((p1 → p1) → (p3 → (p5 → True))) ∨ p5)) ∧ (p1 → p5)))) ∨ p3)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173225409650254738055472523533 : ((True → (((p3 ∨ ((p1 ∨ (False ∧ ((False ∨ False) → p3))) → True)) → p4) ∧ True)) ∨ ((p5 ∨ (p5 → (p2 → ((p4 ∧ False) ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137640631076354822798036105423 : ((False ∨ ((((((p4 ∨ True) → (p5 ∨ (p4 ∨ False))) ∧ p2) ∨ False) ∨ p3) → ((p2 ∧ True) ∧ ((p5 ∨ p4) ∧ False)))) ∨ ((p4 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648920291483298040057148079503 : (((((((p5 ∧ ((((((False ∨ p4) ∧ False) ∧ True) ∧ (False ∨ (p1 → (p4 → p5)))) → p4) → p3)) → p3) ∨ p1) → p2) ∧ (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190386195567670677093561539310 : (((True ∧ ((p5 ∧ p3) ∧ (p3 ∧ (p1 ∨ p5)))) ∨ p2) ∨ (((p5 ∧ False) ∧ p2) → (True → ((p3 ∧ p2) → (p1 ∨ ((p3 ∧ p4) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106118358974795853097570393838 : ((((p5 ∨ ((p3 ∧ (((p4 ∨ p3) ∨ p5) ∧ True)) ∨ True)) ∨ True) ∨ (p1 ∧ (((p3 ∧ (p4 → False)) ∧ False) ∧ (p3 ∨ False)))) ∧ (False → False)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58492316547302137913770677530 : (((p4 ∨ p2) ∧ ((p4 ∧ ((False → p2) → (p4 ∨ (p3 ∨ p4)))) ∧ (((p4 ∧ True) ∧ ((p2 ∨ ((p1 ∨ p2) ∨ p3)) → p3)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782435247237711263205712076969 : (((p3 ∨ (((p4 → ((((p5 ∨ True) ∨ ((p4 ∧ p3) ∨ (p5 ∧ p4))) ∨ (p1 → True)) ∨ (p3 ∧ True))) ∧ (p2 → (p1 ∨ p1))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356644476418600531705461282741 : (p5 → ((((p4 ∧ (p5 → p2)) ∨ (True → False)) ∧ p4) → ((p3 ∧ ((((False ∧ (p3 ∨ (p1 ∧ False))) ∧ (p1 ∨ p2)) ∨ p3) → p1)) ∨ p4))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213643669827106580550217174285 : ((((p1 ∨ p4) ∨ p2) ∨ p5) ∨ (p3 → (False ∨ (False → ((p3 ∧ (((p4 ∧ (((p1 ∧ p3) → p5) → p5)) ∨ p1) ∧ p2)) ∨ (True ∧ True)))))) := by
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
theorem thm_5_vars_199427018500712039875673781561 : ((((p1 → p4) → (p3 → (False ∨ p1))) ∨ p3) → ((p1 ∧ (p4 ∨ (False ∨ p5))) ∨ (((((p3 ∧ p4) ∧ p4) ∧ False) ∧ (p2 ∨ p3)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43315614102604246624249418537 : ((((((p2 → True) ∧ ((p5 ∨ ((p5 ∧ (True → ((p1 → ((p3 ∧ p4) ∧ False)) → p5))) ∧ p5)) ∧ (True ∧ True))) ∨ p5) ∨ p5) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118874502095787418993922329595 : ((True → ((False → p3) ∧ (((False ∧ False) ∧ (((True ∧ (((p1 → (p1 ∨ (p3 → True))) → False) → p1)) ∨ p3) → False)) ∨ p4))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113963435755806679300686578173 : (((True ∧ (((((p5 → p5) ∧ p5) ∧ (((p4 ∧ True) → False) ∧ (p1 ∧ (p2 → p4)))) ∧ p1) ∧ p3)) ∧ (p4 → (p5 ∧ True))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344853923573953005061277773113 : (p2 → (p5 → ((((p3 → ((p3 → True) → (p1 ∨ ((p5 → p2) ∧ p1)))) ∧ p4) ∧ False) ∨ ((p4 ∧ (True ∨ ((p4 → p1) ∨ p1))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258785944480514709173374454074 : ((True → False) → (((p2 ∨ p1) ∧ (((p4 ∨ True) ∧ (p4 ∧ (p3 → False))) → False)) ∧ (((p4 ∨ p1) → p2) → ((False ∧ False) ∨ (p1 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h6.left
    let h14 := h6.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- False on the left can always be used.
    apply False.elim h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h18
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116349553026510742198425977376 : ((((p1 ∨ False) ∨ p3) → (p4 ∨ ((True → False) → ((((p5 → (p1 ∨ (p4 → True))) ∨ p1) ∨ True) → ((p4 → False) ∧ p5))))) ∨ (p4 ∨ p4)) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h9 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h10 := h4 h9
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h12 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h13 := h4 h12
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h15
        -- False on the left can always be used.
        apply False.elim h16
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h19 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h20 := h4 h19
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h23 := h4 h22
          -- False on the left can always be used.
          apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h26 := h4 h25
        -- False on the left can always be used.
        apply False.elim h26
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h29
    -- Implications on the right can always be decomposed.
    intro h30
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h31
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h35 := h29 h34
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h38 := h29 h37
        -- False on the left can always be used.
        apply False.elim h38
    case inr h39 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h40 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h41 := h29 h40
      -- False on the left can always be used.
      apply False.elim h41
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h44 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h45 := h29 h44
        -- False on the left can always be used.
        apply False.elim h45
      case inr h46 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h47 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h48 := h29 h47
        -- False on the left can always be used.
        apply False.elim h48
    case inr h49 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h50 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h51 := h29 h50
      -- False on the left can always be used.
      apply False.elim h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705436063216961670501493374033 : (((((p3 ∨ (p2 ∨ ((p4 ∨ p5) ∧ p1))) ∨ False) ∧ ((p4 ∨ p2) ∧ ((p3 → (((p4 ∧ (p1 ∨ (p4 ∧ p4))) ∧ p1) → p2)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680007562321542052187650895982 : ((((((p3 ∧ p3) ∧ (((p2 ∧ ((p2 → (p1 ∨ False)) ∨ p3)) ∧ True) ∨ (p4 ∨ (True ∧ p1)))) → True) → ((p3 ∧ (p1 → p2)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140347669653604992704480889660 : (((((p2 ∧ ((p4 → ((False → (p5 ∨ p4)) ∨ (True ∨ False))) → p5)) → p2) ∧ (p5 ∨ True)) ∨ ((p4 → p1) ∧ p5)) → (p1 ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214483494715993848394366815858 : (((p1 ∧ p2) ∧ (p4 ∧ p1)) ∨ (p1 ∨ (True ∧ ((False → False) ∨ ((((p3 ∧ (False ∧ False)) ∧ (p5 ∨ p2)) ∧ (p5 → (p3 → p1))) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133761371527109779471157019207 : ((((p2 ∧ (p5 → (p3 ∨ (False ∨ p4)))) ∨ ((p4 ∧ (p1 → False)) ∨ ((True ∧ (True ∨ p5)) ∧ (p1 ∨ p3)))) ∧ p3) ∨ (True ∨ (p5 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669272309389880688447248376398 : (((((p1 → ((p1 ∧ p5) ∨ (p3 ∨ ((((p1 ∧ (p5 ∧ (True → (True ∧ True)))) ∧ p3) ∧ p3) ∨ p1)))) → p2) ∨ (p3 ∨ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309631227121184696277955030540 : (p2 ∨ ((((False ∨ p1) ∨ (p2 ∧ ((p3 → False) ∨ p2))) ∧ ((((p2 → p3) ∨ (p1 → p2)) → (False ∧ p3)) → p1)) ∨ (p2 → (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52896360244941199719028065270 : (((p5 ∨ ((((True ∧ p1) ∨ (p1 → (p3 → p1))) ∨ p3) ∧ (False → p1))) → ((((p3 → p4) ∨ (p2 → p5)) ∨ (True → True)) ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264206424073384761977628315563 : (True ∧ ((p4 ∧ ((p2 ∧ (False ∨ False)) → (True ∨ p1))) → (((p1 ∨ (p1 → (p1 ∧ True))) ∨ p2) ∧ ((p2 ∨ False) ∨ ((p1 ∨ p3) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118319195514359830556480995838 : ((p1 ∨ (p2 → (p1 ∨ (((p3 → p3) ∧ (((((p1 ∨ p5) ∨ True) → p5) ∧ ((True ∨ p3) ∨ (True → False))) ∧ False)) ∨ True)))) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256805695270353223239844411887 : ((p1 ∨ p2) → (p3 ∨ (((p3 → p5) ∨ (p3 → p3)) → (((p2 → (False ∨ ((p2 ∨ p5) → (p1 → p3)))) → p2) ∨ ((p5 ∨ True) ∨ p3))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316713144470397437088526793575 : (p3 ∨ (p5 ∨ (False ∨ ((p2 ∨ (p5 ∧ p2)) ∨ (p5 ∨ (((True ∨ p5) ∨ (p5 → (((False ∨ p3) ∨ True) ∨ False))) ∨ ((p4 → p1) ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_64955917333596470880670715805 : ((p2 ∨ ((((p3 ∧ (p2 → (p3 ∧ p1))) → p2) ∧ False) ∨ ((False ∧ (((True ∧ ((p1 → p2) ∧ p3)) ∨ (p2 ∧ p3)) ∧ True)) → p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_346349133034356010360549012979 : (p3 → (((((p2 → p1) ∧ True) ∨ p3) → ((p2 ∨ (p1 → (((p5 ∧ p2) ∨ p2) ∨ p1))) ∨ ((p1 ∧ p5) ∧ (p2 → p5)))) ∨ (False ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136581650480198978884688328683 : (((p2 ∧ (True ∧ p1)) ∨ ((p2 ∧ ((p1 ∨ ((False ∨ ((p4 ∨ (True → p5)) → p3)) ∧ p2)) ∨ (p5 ∨ False))) ∧ p3)) ∨ (p3 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42657330262393726077784144762 : (((p4 ∨ ((((False ∨ ((p1 ∧ ((True → p2) → ((False ∨ False) → True))) ∨ p3)) ∨ (True ∨ p3)) ∧ p2) ∧ ((p3 ∨ p3) ∧ p2))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78713725406738222415554315823 : ((((((((p2 ∧ (True ∧ True)) ∨ p1) ∨ p4) ∨ p2) ∨ (p4 ∨ (True ∧ p2))) → (p2 ∧ (p1 ∧ (p5 ∨ (False ∧ p3))))) ∧ (p1 ∨ p4)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((((p2 ∧ (True ∧ True)) ∨ p1) ∨ p4) ∨ p2) ∨ (p4 ∨ (True ∧ p2))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (((((p2 ∧ (True ∧ True)) ∨ p1) ∨ p4) ∨ p2) ∨ (p4 ∨ (True ∧ p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28057658174237372874356572682 : (((p4 → p2) → ((((p5 ∨ p1) → p2) → (True ∧ (True ∧ (((False ∨ True) → (p4 → p5)) → ((p4 ∧ p3) ∨ (True → p1)))))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708625053162902200165389370696 : (((((True → ((True ∧ p2) ∨ (True → p1))) ∨ True) → ((p4 ∧ (((True → ((True → (p3 ∧ True)) ∧ (p2 → p3))) → p4) → p1)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259374560506016303445730354941 : ((False → p3) → ((p5 ∨ ((p5 ∨ (((False ∨ ((p5 ∨ False) ∧ p3)) ∨ (p5 → (p3 → ((p5 → p3) ∨ (p3 ∧ p5))))) ∧ True)) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688385062292815687242801351560 : ((((p1 ∧ ((((True ∧ (True → p2)) → (False ∧ (p5 → (p4 ∧ p2)))) ∨ p5) ∧ p4)) ∧ ((p4 → (False → (p1 ∧ False))) → (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191773071253636899480770742369 : ((p1 ∨ ((p4 → (p5 ∧ (p5 ∧ False))) → (False ∧ p3))) ∨ (p3 ∨ (((((p5 → False) → ((False ∧ (p1 ∨ True)) → p2)) → p5) ∧ p4) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → False) → ((False ∧ (p1 ∨ True)) → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229530630539808969893593347826 : ((p2 → (p4 ∨ p5)) ∨ (((p4 → p1) → (p4 ∨ ((p3 → p2) ∨ True))) → (p4 ∨ ((((((p4 → p2) ∨ p5) ∧ p2) ∧ p3) ∨ True) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51934409605424817389838216150 : (((((p5 ∧ (True ∨ ((p3 ∨ p3) ∧ p2))) ∧ p1) ∧ ((p1 ∨ (p3 ∧ p2)) → p3)) ∨ (False ∧ ((p4 ∧ p2) ∨ (True ∧ (True → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661624389667624875643098714725 : ((((((False ∨ (True ∨ (p1 ∨ ((((p4 → ((p5 → False) → p3)) ∧ True) → False) → p1)))) → p2) → ((p3 ∧ False) → p1)) → (p3 → p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51203819630176180540119306088 : ((((((p3 ∧ (False → p5)) → (p1 ∧ p4)) ∧ (p1 ∨ p1)) → (False ∨ (p2 ∨ (p4 ∧ p3)))) ∨ (True ∧ ((p4 ∨ True) ∨ (p3 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305864993370829777714797839956 : (p1 ∨ (((((True ∨ p4) ∨ True) → False) ∨ p3) ∨ (((p1 → False) ∧ p4) → (((((True ∨ p5) → p2) ∧ (False ∨ p4)) → p2) ∧ (False → True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750223399517469964021271773577 : (((True ∧ ((p2 → (((((p4 → True) → (False ∨ p2)) ∨ ((p1 → p4) ∨ (p4 ∨ p2))) ∧ p5) ∨ (p4 → (True ∧ False)))) ∧ (p2 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51310327837904182331954757507 : (((p3 ∨ ((p5 ∨ (p2 ∨ (p1 → (((((p1 → p4) ∨ True) ∧ p5) ∧ False) ∧ p2)))) ∧ p2)) ∨ ((True ∨ ((False ∧ p1) → p4)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344127294937939297496776366648 : (p2 → (False ∨ ((p2 ∨ (p3 → (p3 ∨ (p5 ∧ ((p3 ∧ p3) → (p1 ∧ p3)))))) → (((False → p3) ∨ (False ∨ (p2 ∨ p1))) → (p1 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180345309015644337058685853367 : (((p1 → ((((p2 → p1) ∧ p5) ∨ p2) → (p4 ∧ True))) ∧ (p2 ∧ p4)) → (p1 → (p2 ∧ (p4 ∧ ((p1 → ((True → False) ∧ p5)) → p5))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h16 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h17 := h11 h16
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h19 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h20 := h18 h19
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3237487731020586052342799977 : ((p3 ∨ p2) ∨ (((True ∧ p3) → ((True → (True ∧ (p5 → (p3 ∨ (False ∨ (p3 ∧ (p5 ∧ p1))))))) → (p2 ∨ (p5 ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752050104510209452551324705523 : (((True ∧ (True → ((p3 ∧ p1) ∨ (((((False → p2) ∨ ((p2 ∨ p4) ∨ p3)) → (False → ((p3 ∧ False) ∨ p3))) → p1) ∨ (True ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636052267218705656944438505202 : (((((p1 ∧ (((p1 ∨ (p2 ∨ True)) ∧ (p2 ∨ ((p3 → p3) ∨ False))) → (True ∧ p2))) ∧ ((((p1 ∨ p2) ∧ False) → True) ∨ p2)) → p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p1 ∨ (p2 ∨ True)) ∧ (p2 ∨ ((p3 → p3) ∨ False))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322359595081292637005648717871 : (p5 ∨ (((p1 → ((p3 → p2) → ((p4 ∧ False) ∧ (True ∧ (True ∨ ((p2 ∧ p4) ∧ (True ∧ (False ∨ p5)))))))) ∨ ((False ∨ p3) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777482222972906076568013667960 : (((p1 ∨ ((p2 ∨ ((p5 → p2) ∨ (True ∨ ((p3 ∨ (p2 ∧ (True ∨ True))) ∧ True)))) ∧ ((p5 ∧ p2) ∨ (((False ∧ p4) ∨ True) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685785602799050536021364036443 : (((((((p2 → p1) ∨ ((p5 ∧ ((p4 ∧ (p1 ∧ False)) ∨ (p1 → True))) → p3)) → p2) → p2) → ((p2 → ((p5 ∧ p2) → p3)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187440538009210653151975888211 : ((p5 ∧ (True → (p4 ∨ (((p3 → (False ∨ p5)) ∧ p2) ∨ p3)))) → ((((p1 ∧ (False ∨ False)) ∧ p1) ∨ p1) ∨ (((True ∧ p1) ∨ p1) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136206390240720068117563833265 : (((p4 ∨ ((p3 → p2) → (p3 → p4))) ∧ (((p4 ∨ (p5 → p2)) → ((p4 ∧ p4) ∨ (True → (True → p3)))) → False)) ∨ (False ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135755103218873490176421943724 : (((p1 ∧ ((False → p5) → (((p2 → (p5 → (p4 ∧ p1))) → False) ∨ False))) ∨ (False → (True ∧ ((p5 → p4) ∧ True)))) ∨ ((p3 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40749332152909861706750742073 : (((((True ∧ True) ∧ (((((p3 ∧ ((p5 → ((p5 ∨ p1) → p3)) ∨ p2)) → False) ∨ ((p4 ∧ True) ∨ p4)) ∧ True) → p2)) → p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185389947439098919616082903276 : ((p5 ∧ (False ∨ ((False ∧ p4) → (p1 → (p5 ∧ (p5 ∧ True)))))) ∨ (True ∧ ((p2 ∨ p2) ∨ ((False ∧ ((p3 → True) ∧ (True → True))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68076679316699269514564900717 : ((p2 → (p3 ∨ ((p3 ∨ ((((p3 ∧ (((False ∧ (True ∨ True)) ∨ (p5 ∧ (p1 ∨ p5))) → p3)) ∨ p1) → p1) → (False ∧ True))) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563328051692582381562898934855 : (((p5 ∨ (((p3 ∨ p5) → p1) ∨ (((p1 ∨ (p2 ∧ False)) ∨ ((p2 ∧ (p4 ∧ False)) ∧ False)) ∨ (False → ((p3 ∨ True) ∨ (p2 ∨ p5)))))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709459286152807029622778398690 : ((((p3 ∧ (((p5 ∨ (False → True)) ∨ True) → True)) → ((p5 ∨ ((p2 ∨ p1) ∨ False)) → (False ∨ (p4 ∨ ((False ∨ p3) → (True → p3)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Implications on the right can always be decomposed.
        intro h23
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747704915374299021735668494289 : ((((False → True) → (p4 ∨ ((((True ∨ (((p4 ∨ ((False ∧ p4) ∧ p3)) → (p3 → p4)) ∨ p1)) ∧ p5) → ((True ∨ p2) → p2)) ∨ True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205339062868793480462639060201 : (((p4 → (p5 ∧ p2)) ∨ (p4 ∧ p5)) ∨ (((((True ∨ (((p4 ∧ p3) ∨ p2) → p3)) ∨ (p5 → False)) ∨ False) → (p3 ∧ p4)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786424299434962579828055526362 : (((p4 ∨ (((((p4 ∨ False) → False) ∧ p5) ∨ (p3 → (p4 ∧ ((p2 → p2) ∨ p4)))) ∨ ((p3 → (p2 ∧ (False ∧ False))) ∧ (p1 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614746828378513658368227213422 : (((((((p2 → p2) ∨ ((p1 ∨ (p3 → p4)) ∨ (p2 ∨ (p3 → p4)))) → (p4 ∧ (p3 ∧ p3))) ∨ (True ∨ (True ∧ (p2 → p3)))) ∨ p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_668038403878614918831737466859 : ((((p5 ∨ ((((False → ((p3 ∧ False) ∧ True)) ∧ ((p2 ∧ (p3 ∨ True)) → (False → p2))) ∨ True) ∧ (p2 ∧ p4))) ∧ ((p3 ∨ p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241840341009301320646302048904 : ((p1 → p1) ∧ ((((p2 → ((p1 ∨ True) ∨ (True ∧ ((p3 ∨ p3) → p2)))) ∨ (False ∨ False)) → False) → (p3 ∨ (((p5 ∧ p3) ∧ p1) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 → ((p1 ∨ True) ∨ (True ∧ ((p3 ∨ p3) → p2)))) ∨ (False ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705400329464687867791637246985 : ((((((p5 → False) → (p1 → (p1 ∨ p2))) ∨ False) ∧ ((p5 → ((p1 ∨ (((p3 ∧ ((p5 ∨ False) → p5)) → p3) → p5)) → p5)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737639323897421450552697204506 : ((((p5 → p3) ∧ ((False ∧ ((p2 ∧ (((p3 ∧ True) → (p1 ∨ p4)) ∧ True)) ∨ (p2 ∧ (p1 → (False ∧ (p4 ∨ (p4 ∧ True))))))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190194986934166495162799713155 : (((p2 ∨ ((p3 → (p2 → p4)) → (p4 ∨ p4))) ∧ True) ∨ (False → (((p2 → (p3 ∨ p5)) ∨ (p2 ∧ (p2 → p4))) ∨ (False ∨ (p1 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256123145643787425927864219227 : ((True ∨ p5) → (((True → p4) → p1) → (((p3 ∧ (False ∨ (((p5 → (p4 ∨ p5)) ∨ p3) → p4))) ∨ False) → ((p1 → p2) ∨ (True ∧ p3))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37675656574264064895396851546 : ((((((((((p4 ∨ True) ∧ (False → ((p4 ∧ (p4 → p2)) → p2))) ∧ (p1 ∧ True)) ∧ p5) → p5) → p1) ∧ (False ∨ True)) → False) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166564360991610354494253943044 : ((p5 ∨ (p4 ∨ (False ∨ ((p2 ∧ p2) ∧ (((True → (p3 ∧ p3)) ∨ p5) ∧ (p2 ∨ p2)))))) ∨ (((p5 → p4) ∨ p1) ∨ (p3 → (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309815843378063287208765750880 : (p2 ∨ ((False ∨ (p2 → ((((p1 ∨ p2) ∧ ((p4 ∧ ((False → p4) → (False → p2))) ∨ True)) ∨ p2) ∧ False))) ∨ (((True ∧ p4) ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



