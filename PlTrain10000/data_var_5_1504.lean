variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358097232567530789791992695104 : (p5 → (p2 ∨ (((p1 → False) → (True → (p1 ∧ ((p5 ∧ p2) ∧ (((p2 → (p2 → p2)) ∧ ((False ∨ p2) → p2)) ∧ (True → p3)))))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201250579035098617311541649325 : ((p3 → ((True → ((p1 → False) ∨ p5)) ∨ p5)) → ((p2 → p2) ∧ (((True → ((p2 ∧ True) → p3)) ∨ False) ∨ (((p4 ∨ False) ∧ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119368445323745944496214073801 : ((p3 → (p1 ∨ (((p4 ∧ p5) → (False ∨ ((p3 ∨ (p3 → (((p3 → ((p4 → False) ∨ True)) ∧ p5) ∨ p2))) ∨ p5))) → p4))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57157987793385737337820260396 : ((((False ∧ p4) ∨ False) ∨ (False ∨ (p1 ∨ (((False → p4) → (((p1 ∨ p4) ∨ True) → ((False → p1) ∧ p2))) → ((p5 → p5) ∨ p3))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178596763773235789229036355460 : (((((True ∧ p3) ∧ True) → (p4 ∨ p2)) ∨ ((p4 ∧ p4) ∨ (p1 ∧ p2))) ∨ (((p4 ∧ p4) ∧ (p3 ∧ p3)) → (p3 ∨ (p1 ∨ (False ∧ p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164690715222427561515843174938 : ((((((False → (True → ((p4 ∨ p3) → ((False → p4) → p4)))) → p3) ∧ p5) ∨ p3) ∨ p5) ∨ (p3 ∨ ((p4 → (p2 → p4)) ∨ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711834360359664901194607285626 : ((((((True ∨ True) → (p4 ∨ p2)) ∧ p2) ∨ ((p2 ∧ ((True ∧ ((p1 ∨ p4) ∧ p4)) → (((False → (p2 ∨ p4)) ∨ True) ∧ True))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324174705377880592118388178346 : (p5 ∨ (((False → p2) ∧ (((p2 ∨ p4) ∧ (p1 → False)) ∧ p1)) ∨ (((True ∨ (p1 → True)) ∨ p5) → (((True → False) → p4) ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137206328100494805782620155127 : ((False ∧ (p5 ∨ ((p1 ∧ ((True → (((p2 → p5) ∨ ((p2 → (p4 ∨ p3)) ∧ p2)) → p2)) ∧ p4)) → (p3 ∧ p1)))) ∨ ((True → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727804082445161482552493085685 : ((((p1 ∨ (False ∧ p2)) ∨ (((p5 → ((False → p1) ∨ (p2 ∧ (True ∨ (p3 → (((False → p1) → (p5 ∧ p5)) → p2)))))) ∧ p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204575751886028326782146230734 : ((((False → p4) ∧ (False ∧ p4)) ∨ p5) ∨ ((False ∧ ((((p5 ∧ p5) ∨ ((p3 → p2) → (p3 ∧ ((p4 → p3) ∨ p2)))) ∧ p3) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314254433753009722137392191362 : (p3 ∨ (((p5 ∨ ((False ∨ ((p2 ∨ True) → p2)) ∧ p2)) ∧ (p3 → (p4 ∧ (True ∧ (((False ∧ True) ∨ p2) → p1))))) ∨ (p3 → (p5 → p5)))) := by
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
theorem thm_5_vars_191482443173576198542305851790 : ((True ∧ (((p3 ∨ p1) → p1) ∨ (p4 ∧ (False ∧ p5)))) ∨ ((p4 ∨ p5) ∨ (False → ((p3 ∨ p5) ∨ ((p3 ∧ (p4 ∧ p1)) → (p4 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313224156755382977502822392997 : (p3 ∨ (((p5 → (p4 ∨ p4)) → (p4 ∧ ((p3 ∨ (((p2 ∧ p1) ∧ (True ∨ (True ∧ (((False ∨ p5) → False) → p2)))) ∨ True)) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341732659146321863575369446156 : (p2 → (((True ∧ p5) ∧ ((True ∧ p1) ∨ ((p4 ∨ (False ∨ (p3 → ((p2 ∧ p5) ∨ ((False ∨ p3) ∧ p1))))) → (p4 → p5)))) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208056725046017470618791941100 : (((p1 ∨ (p2 → p2)) ∨ (False ∧ p3)) → (p2 ∨ (True → ((p4 ∨ p5) ∨ ((True ∨ p1) ∨ (p5 ∨ (True → (p5 → (True ∨ (True ∨ p3)))))))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39213687349708474888164938653 : (((True ∧ (((False ∨ (p1 → ((False → ((p1 → p5) ∨ p2)) → p2))) ∧ p5) ∨ (((p3 ∨ False) ∨ (p4 ∨ (False ∨ p3))) → p4))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244088858232833344358953053183 : ((True ∧ p3) ∨ (((((p3 ∨ (p3 → False)) → p1) ∨ True) ∨ (((True → p3) ∨ False) ∧ False)) → (((True ∧ p5) ∨ ((p4 → False) ∧ True)) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623743572225888630655849383254 : ((((p1 ∨ ((((p1 ∨ ((((p3 → True) ∧ False) ∧ (True ∧ p5)) ∨ p2)) ∨ (False → p4)) ∨ (p4 → p2)) ∨ (p2 ∨ (p2 ∨ True)))) ∨ p3) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40895214150499496994579917421 : ((((((p1 ∧ p4) ∨ p2) ∨ (p5 ∧ (((p2 ∨ p1) → (p3 ∨ (((p2 ∧ (True ∨ True)) ∧ p2) → p1))) ∨ p4))) ∧ (False ∨ p2)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200827142515848388885161898277 : ((p5 ∧ (True → (False ∨ (p1 ∨ (p4 ∧ True))))) → ((p2 → (p1 ∨ p5)) ∧ ((((False ∨ (p2 ∨ (False ∨ p1))) ∨ p3) ∨ (p5 ∨ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184513213498832465209952008167 : (((p2 ∧ (False ∧ ((p3 ∨ p5) ∨ (False ∨ p3)))) ∨ (False → p5)) ∨ (((p1 → ((((p2 ∧ (True ∨ p1)) ∨ p1) → p2) → p1)) ∨ p2) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172255382958751056590158363793 : (((True → ((True ∨ p5) ∧ (p3 ∨ (p5 ∨ False)))) ∧ (p3 ∨ ((p3 ∧ p4) → True))) ∨ ((False → p2) ∧ ((p3 ∧ p4) ∨ ((False ∧ p4) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_200773644373458733939077478028 : ((p4 ∧ (((p5 ∧ False) ∨ p1) → (False ∧ p4))) → ((True ∨ p3) → ((p3 → (((p3 ∧ p4) ∨ False) → p2)) ∨ (((p5 ∨ p2) ∧ p5) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56026258413026737465816698989 : ((((p2 ∧ (p5 ∧ p1)) ∨ p5) ∨ (p3 ∨ ((p5 → ((p1 ∧ (p3 ∨ (True ∨ p1))) ∨ (p1 ∧ False))) ∨ (False → ((False → p3) → p4))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261196580350384416335301935994 : ((p4 → p5) → ((True → (p5 ∨ (p4 ∧ (((p5 ∧ (((True → False) → False) → (p5 → p3))) ∨ ((p4 ∧ (True ∧ False)) ∧ False)) ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157733451283129985564062060998 : (((False → (((p2 ∨ (((p2 → p4) → p4) → False)) → (p5 → False)) ∧ True)) → ((p2 ∨ p2) ∨ p1)) ∨ ((False → ((p1 ∨ True) → p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601506033460744948046419490148 : ((((p3 ∧ ((True → ((True ∨ ((p1 → p5) ∨ (p3 → ((p3 ∧ (p2 ∧ False)) → p1)))) ∧ (((p4 → p4) ∧ p5) ∨ False))) → p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217252718177730730970476943786 : (((False ∧ (False → False)) ∨ p4) → ((p2 ∧ ((p2 → ((((False ∨ p5) ∧ (p1 → (False ∨ p3))) → p3) ∨ ((p3 → p5) ∧ False))) ∨ False)) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117272607986452218521293715578 : ((False ∧ ((((p4 ∨ (((True ∨ p3) ∧ p5) ∨ ((p4 ∨ p2) → (p3 ∨ ((p3 ∧ (p5 ∨ p5)) ∧ p2))))) ∨ p3) ∧ p1) ∨ True)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157024441169839463790105126821 : ((((True ∧ p4) ∨ ((True → p5) ∨ (((False ∨ p3) ∨ p5) ∧ (p2 ∨ ((p1 ∧ p4) → p1))))) ∨ p2) ∨ (True ∨ ((p5 ∨ (p1 ∨ p3)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133659345607952817774941840171 : (((((((p2 ∨ ((p4 ∨ p2) ∨ True)) ∨ p4) ∨ p2) → (((True ∨ p1) → p2) → (p3 ∨ p5))) ∨ (p2 ∨ False)) ∧ p4) ∨ (p5 → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732242403171334241544427256915 : ((((False ∧ True) ∧ (((p1 ∨ ((p3 ∧ p4) ∧ (p5 → p1))) → (p5 ∨ (((True ∧ p2) ∨ (p4 → (p5 ∨ (p4 → p3)))) → p5))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329575851350857978008925336736 : (True → ((p4 ∨ p2) ∨ (((p4 ∧ (p2 ∧ p4)) ∨ ((p5 ∨ p2) ∧ ((((p2 → p4) ∧ True) ∨ ((p2 ∨ (p3 ∨ p4)) → p2)) ∧ p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134925903653117649316640768610 : (((((p1 → (False → (((False → False) ∧ ((p4 ∧ (p1 ∨ (p1 → p4))) → False)) ∧ p1))) ∨ True) → False) ∧ (False → p5)) ∨ (False ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763017286313672944247776257126 : (((p3 ∧ (((p3 ∨ p2) ∧ p1) ∧ ((p2 ∧ ((p1 ∨ p5) ∨ p4)) ∧ (((((p2 ∧ ((p5 ∧ p4) → p5)) → p4) ∨ p1) → True) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_486271518974567456108832784973 : (((((p5 → p1) ∨ (p4 ∨ (p4 ∨ p5))) ∨ (((((p3 → p5) ∧ (False ∨ p3)) ∨ (p2 → False)) ∧ p3) → (p2 → (False ∨ (p3 ∨ p4))))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617745412033383063738742817810 : (((((p4 ∧ (((p3 → p1) ∧ p5) → False)) ∨ (p4 ∧ (False ∨ ((p1 ∨ (False → (p1 → (p4 ∧ True)))) ∧ ((p2 ∨ p1) ∧ p2))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_50281240831158950195096987363 : ((((((p1 → ((p4 ∨ ((p4 ∧ p1) ∧ p3)) → ((True ∨ p5) ∧ p3))) ∨ p1) ∨ p1) → (False ∨ p3)) ∨ (((False → p1) → p2) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216041134164201009617054806250 : ((p5 ∨ ((p1 → p3) → p5)) ∨ ((False ∧ ((((((True → p4) → ((p3 ∨ False) → True)) ∧ False) → (p2 → p5)) ∨ (True ∧ p4)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355186674005737432867167354759 : (p5 → (((((p4 ∧ ((p5 ∧ ((p4 ∧ True) → True)) ∨ p3)) ∧ p4) ∨ p1) ∧ (p5 → (((False → p2) ∨ p4) ∧ ((p1 ∨ True) → False)))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h21 := h4 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : (p1 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h24 := h22 h23
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224930745166338650083581668899 : ((p5 → (p5 ∨ p5)) ∧ ((((False ∨ ((p5 ∨ ((p5 ∨ p4) ∧ (p3 ∧ (p2 → p3)))) ∨ p3)) ∧ False) ∨ ((p5 ∧ True) ∨ p4)) ∨ (False → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61956986207451056375054503144 : ((p2 ∧ (((p5 ∨ (p3 ∧ ((p3 ∧ (p2 ∨ p4)) ∨ p5))) ∧ (p1 → (p1 ∧ p2))) → ((p1 → ((p2 ∨ (p4 ∧ p3)) ∨ p2)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137636241738167140598535241527 : ((False ∨ (((((p4 ∨ p2) ∧ p2) ∨ (((False → p2) ∧ False) ∧ (p5 ∨ (p5 ∨ p3)))) → False) → (True → (p4 ∨ False)))) ∨ (p1 → (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41643391001232790786988352969 : (((((((p4 → p3) → p1) → False) ∨ False) ∧ ((((p5 ∨ False) → (False ∨ p3)) ∨ (p3 → p1)) → (p5 ∧ ((False → True) → p5)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183761666170726993300698745560 : ((p5 → (True ∨ ((p1 ∨ (p3 → (True ∨ p5))) ∧ (False → True)))) ∧ (((p4 → False) ∨ (p4 ∨ (((p5 ∨ (p2 → True)) → p3) ∨ True))) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113246031248846535320441593600 : ((((p5 ∧ ((p5 ∨ (True → ((p4 → False) ∨ (p2 ∨ p4)))) ∧ ((p4 ∧ p1) ∧ (p2 → p4)))) ∧ (True ∨ p5)) ∧ (p2 ∧ True)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114901555588185376026390611887 : (((p3 → (p1 ∨ ((False ∧ (True ∧ (p1 → (False ∨ p3)))) ∧ (p5 ∧ False)))) ∨ (((p4 → (p5 ∧ (p5 ∧ p5))) → False) → True)) ∨ (p5 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689113789445188600092550559259 : (((((p3 → ((p2 → (p2 ∧ (p5 → (((p5 ∨ p3) ∨ p2) → p3)))) → p5)) ∨ False) ∨ ((True → False) → (False ∨ ((p5 ∨ p4) → True)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46270536734356538679728849931 : (((((((p5 → False) ∧ (False ∧ ((p2 ∧ p1) ∧ (True → p3)))) ∨ ((p1 ∨ False) ∧ p3)) ∧ p2) ∧ ((True → p3) ∨ p2)) ∧ (p4 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70709081811311268704398608979 : ((((p3 ∧ (False ∨ ((p3 ∧ (((True → p5) → ((False → False) ∧ p2)) → False)) ∨ p4))) ∧ (False → ((p5 ∧ (True ∧ p3)) → p2))) ∧ p2) → p4) := by
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
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : ((True → p5) → ((False → False) ∧ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h13
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693540815696214835162280188911 : (((((((False ∨ p2) ∨ p4) ∨ (True → (((p1 ∧ p5) → p4) ∨ False))) ∧ False) ∨ (False ∧ (p1 ∧ (((p1 → p1) → (True → p3)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608260517785601821097285322778 : (((((((((p5 ∧ p5) ∧ (((p4 ∧ (True → True)) → p2) → ((((p5 → p3) → p4) → p5) ∨ p2))) ∨ False) → p4) ∨ p1) ∨ True) ∨ p1) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_353366102310780863917729564686 : (p4 → (False ∨ (((p2 → (p5 ∨ p2)) ∧ ((p1 ∧ ((((p5 → False) → ((False ∨ p3) ∨ False)) → False) → p5)) ∧ p5)) ∨ ((False ∧ False) → True)))) := by
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
theorem thm_5_vars_184673352443470808267033395781 : (((p1 ∧ (((p2 ∧ p1) ∨ p5) → False)) ∨ ((False ∨ p1) ∧ p2)) ∨ (p4 → ((p3 ∧ ((False ∧ p3) → (p3 → (p5 ∨ p2)))) → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49794601854027310411596723594 : (((p5 ∨ (((p3 ∧ (p3 ∨ ((True ∨ True) ∨ (p5 → (True ∧ p2))))) → p5) → (((p3 ∨ p4) ∨ p1) ∧ p2))) → ((False → p5) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152803595942665939602224979415 : (((True ∨ p3) → (((p3 → True) → (p3 → (((p3 ∧ p5) ∧ (True ∧ (p4 ∧ p1))) → p2))) ∧ (p3 ∧ False))) → (p4 ∧ ((p2 ∧ p1) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149151179090645848959193303211 : (((p1 ∨ True) ∧ (((((p1 ∧ ((p1 → (p1 ∨ True)) ∧ p1)) ∧ (False ∧ p5)) ∧ p3) ∨ (p1 ∨ p1)) ∧ p2)) ∨ (p4 ∨ (True ∨ (False ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317682063511334900639951089974 : (p4 ∨ (((p2 ∧ (((((((False ∨ p2) → False) ∧ False) ∧ p1) ∨ (p3 ∧ p2)) ∧ (False ∧ ((p1 → (p1 ∧ False)) → p2))) → p5)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89405610301836238703777860385 : (((p3 → (p4 ∧ p3)) ∧ (((p4 → (((p4 ∨ (p1 ∧ ((True ∧ p2) ∧ p2))) → p3) ∨ (True ∧ (True ∨ True)))) ∨ (True ∨ True)) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → (((p4 ∨ (p1 ∧ ((True ∧ p2) ∧ p2))) → p3) ∨ (True ∧ (True ∨ True)))) ∨ (True ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735390357549495491634218947190 : ((((p4 ∨ p2) ∧ ((((((((False ∨ p3) → (False ∧ p5)) → ((p5 ∨ p3) ∨ True)) → p1) → (False ∧ p4)) ∧ p3) ∧ (p4 ∨ p1)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312423310106337610416935498765 : (p2 ∨ (p4 → ((p1 ∧ (((p1 ∧ False) → ((False ∨ False) ∧ (p2 → ((p1 → (((p2 ∨ p3) ∧ True) ∧ False)) → p1)))) → p2)) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_263416895765692144923129328436 : (True ∧ ((p1 ∧ ((p1 ∨ (((((p3 ∧ p2) ∨ (p1 → p5)) ∧ p2) ∨ p2) ∨ (p2 ∧ p3))) ∧ ((p4 → p5) → True))) ∨ ((p1 → p5) → True))) := by
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
theorem thm_5_vars_688423060671805795018353136207 : ((((p2 ∧ (False ∧ (((p2 ∨ p1) ∧ p1) ∧ (((p2 ∨ p3) → False) → (True ∧ p4))))) ∧ (p5 → (((p4 ∧ False) → False) ∧ (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178539578883787521440190933756 : (((True ∨ (((p1 → p2) ∧ True) ∨ (p4 ∧ p3))) → (p4 ∧ (p4 ∧ p4))) ∨ ((p2 ∨ (p1 → True)) ∨ (((p1 ∨ (p3 ∨ True)) ∧ p1) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310048080387549222361847261121 : (p2 ∨ ((((((p3 ∧ p5) ∨ p1) ∧ (((p1 ∨ p2) ∨ p3) → (p4 ∨ p4))) → True) ∧ p3) → ((p1 ∧ (False ∧ p2)) ∨ (p5 ∨ (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228868741865138622160964105342 : ((p4 ∨ (True ∧ False)) ∨ ((((p2 → p1) ∧ p1) ∧ p2) ∨ ((p2 ∨ ((p4 → ((True → p1) ∨ ((p2 ∧ p4) ∧ p2))) → (p2 ∧ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163499472436164265141782232681 : (((False ∧ (p3 ∧ p3)) ∨ ((True ∧ p2) ∨ ((p3 ∨ p4) → (p3 → ((p3 ∧ p1) ∨ p3))))) ∧ (((p2 → p5) ∨ (False → (p5 → p3))) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768987079854359347263931407661 : (((p5 ∧ ((True ∧ (p1 ∨ False)) ∧ (((((True ∧ p2) ∧ p3) ∧ ((p2 ∨ p3) ∧ (p2 ∨ p3))) ∧ (p1 ∨ p1)) ∧ ((False ∧ p1) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732170344544572796452764161232 : ((((True ∧ p4) ∧ ((((p2 → (((((True ∨ (True ∨ (p1 ∨ p3))) → p2) ∧ p2) ∧ p2) ∨ p3)) → True) ∧ (p1 → (p2 ∧ p3))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43402225603045993770986874968 : ((((((p2 ∧ p3) ∨ ((p4 → (p1 ∧ p1)) ∧ ((p5 → False) ∧ p4))) ∧ (False → ((p5 ∨ False) → ((True ∨ p1) ∧ p5)))) ∨ p2) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204656702692813490881858701922 : (((p4 ∧ ((True → p3) ∧ p1)) ∨ False) ∨ (p2 → ((True ∨ (p1 ∨ (p1 → p1))) → (p2 ∧ ((p1 → (p2 ∧ p4)) → (False ∨ (p2 ∨ p1))))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623742945354247196730505620437 : ((((p1 ∨ (((p1 ∨ ((False ∨ ((p2 ∧ p1) → (p4 ∨ ((p3 ∨ p3) ∧ (p3 → p4))))) ∨ p5)) ∨ True) ∨ ((p4 ∧ p2) ∨ p3))) ∨ p1) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115371079831276800371827129073 : (((((True → (p2 → p5)) ∧ p5) ∧ (p2 ∧ False)) ∧ (((p1 ∨ (p4 ∨ p1)) ∨ False) ∨ ((True → (p5 → p1)) ∧ (p3 ∧ p5)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198168388273729447428239465108 : (((p2 ∨ p3) → ((p2 ∧ (p1 → False)) ∧ p1)) ∨ (True ∨ ((p1 ∨ p1) → (((False ∨ p4) ∨ (True ∧ False)) ∧ ((p3 → (p5 → p1)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60297954169107712824586214108 : (((p1 → p1) → (((p5 ∨ p5) ∧ p3) → (((p1 ∨ (False ∧ (p1 ∨ (p3 → (p3 ∧ (p3 ∧ p1)))))) → p2) → ((True → p3) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113580437914819775268538365025 : (((p1 ∧ (((((p1 → (((p5 ∧ p2) ∧ (p2 ∧ p3)) ∨ (p1 → p5))) ∧ p1) → p1) → p1) → (p3 ∨ p5))) ∨ (p3 ∨ True)) ∨ (True → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330537531159910451659736848422 : (True → (p5 ∨ (((p3 ∧ ((False ∧ (((True ∨ True) ∨ (p4 ∨ p3)) ∧ p3)) ∧ (p4 ∨ (p3 ∧ ((p1 ∧ p1) ∨ (p5 ∨ p2)))))) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803791848810890399976792078642 : (((p3 → ((((((False → p5) ∧ p4) → ((((p3 → p1) → False) ∨ p2) ∨ ((p1 ∧ (False → True)) ∨ True))) ∨ False) ∧ p4) ∨ (True ∧ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232077608519625831656945136921 : (((p4 ∨ p2) → p5) → ((p3 ∧ ((p4 ∧ p2) ∨ ((p2 ∧ (p3 → True)) ∧ (((p3 ∧ True) → ((True → p5) ∨ p1)) ∧ (p2 ∧ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340772465297212877447457045331 : (p2 → ((((((p2 → ((True → p5) → p5)) ∧ ((p4 ∨ p1) → (p5 ∨ (False ∨ p3)))) ∧ (((False → False) ∨ p2) ∧ True)) ∨ p1) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936578564240652820625461113700 : (((((False ∨ (True → (p4 ∧ p5))) ∧ p4) ∧ ((((p3 → False) ∨ (False ∧ p5)) ∧ (p1 ∧ ((True → p4) ∧ ((True ∨ p2) → p2)))) → p5)) → p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38247174773636998033218137154 : (((((((False ∨ p3) ∧ (((True ∨ p1) → p4) → p3)) ∨ (False ∨ True)) ∨ ((False ∧ False) → p3)) ∧ ((p1 ∧ p4) ∨ (p2 ∨ p2))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185060371679085121500385291910 : (((p1 ∧ p3) ∨ ((False → True) → ((p5 ∨ p1) → (True ∧ False)))) ∨ (True ∧ (p4 ∨ (p3 → (False → (p1 → ((p2 ∨ True) ∧ (p4 ∧ p1)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158723077347947572440992859810 : ((p3 ∧ (((False ∨ True) → ((True ∧ p5) → p4)) → (p3 → ((p1 ∧ p4) ∨ (p3 ∧ (p5 → p1)))))) ∨ (True ∨ ((p5 ∧ (p5 ∨ True)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118218446146428538488683327726 : ((p1 ∨ (((((p5 → (((((p3 ∨ p1) → p1) ∨ p4) ∨ (p2 → p1)) ∧ (False ∧ True))) ∨ p5) ∧ (True → p4)) ∨ p2) ∨ p3)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40142735117757654629598570541 : ((((((((False ∧ p3) ∧ p5) ∨ (p1 ∨ (p4 ∧ ((True ∧ p5) → p3)))) → False) ∧ ((True → p2) ∧ ((p3 ∧ True) → p1))) ∧ p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342214968410519218447471660054 : (p2 → (((p2 ∨ False) ∧ ((p2 ∨ (p1 → (((p5 ∧ p5) ∨ p1) ∨ ((p3 → False) ∧ (p4 → True))))) ∨ p3)) → ((p4 → False) ∨ (False → p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249684731216046162858726296357 : ((p5 ∨ p4) ∨ (((p2 ∨ p2) ∨ p5) ∨ (False → (((((p5 → ((p4 → (False → p1)) ∨ p4)) ∧ p1) → p1) ∨ p5) ∧ ((p2 ∧ p3) ∧ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721258830249523330344734616896 : (((((p3 ∨ p2) → (False ∧ p3)) → (((((p1 ∧ p2) ∧ False) ∧ p5) ∨ p3) ∨ (((p4 ∨ True) ∧ (((p5 → True) ∨ p1) ∨ True)) ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48020182609403554858324890902 : ((((((p5 → p3) ∧ p2) ∧ (p5 → (p3 → ((p3 → True) ∨ p3)))) ∨ (True ∧ (((p4 → (p2 ∧ p1)) ∨ p5) ∧ p1))) → (p5 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178545422101942196390537658493 : (((p1 → ((p4 → p3) ∨ ((p4 ∧ True) ∧ p1))) → ((p1 → p3) ∨ p1)) ∨ ((((p4 ∧ (p1 ∧ p2)) ∧ (True → True)) → p2) ∧ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56316397925659717972804425132 : ((((p1 ∨ (False → p5)) ∧ p3) → ((p2 ∧ ((((p1 ∨ False) → True) ∧ (((p2 ∧ True) → False) ∧ p3)) ∨ (p5 ∧ p2))) ∨ (p5 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349418981469647227346041742158 : (p3 → (p4 → ((((p4 → p5) → (((p2 ∨ p5) ∨ True) ∨ p1)) → False) ∨ (((p4 ∧ ((False → (False ∨ (False ∧ p4))) ∧ p3)) ∧ True) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65761148715499205946505344894 : ((p4 ∨ ((((p1 ∨ p1) ∧ ((((p3 → ((p1 ∧ p5) ∧ (p3 ∧ p4))) ∨ p1) → False) → p3)) → p3) → (True ∧ (p3 ∧ (p1 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204650721547298327333555707663 : (((p3 ∧ ((p4 → p3) ∧ p2)) ∨ p1) ∨ ((True ∧ ((p1 ∨ (False → False)) ∨ True)) ∨ (True ∧ (((p5 ∧ ((True ∨ p1) → False)) ∨ p4) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628098191053976510233152869089 : (((((((p1 → p3) ∧ p2) ∧ ((((p1 → p2) ∨ p1) ∧ (p1 ∧ p3)) → (p2 ∧ (p1 ∨ (False ∧ (p2 → (p4 → p5))))))) ∧ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233063598472582154977421031762 : ((p4 ∧ (p3 ∨ False)) → ((((p3 ∨ p2) ∧ p5) ∨ p2) → (((p5 → ((p1 → p4) ∨ p4)) → p1) → (p5 ∨ (False ∨ ((p1 ∧ p1) ∧ p3)))))) := by
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
      let h8 := h1.left
      let h9 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h21 : (p5 → ((p1 → p4) ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h23 := h3 h21
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h23
      -- One of the premise coincides with the conclusion.
      exact h23
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115213655191897171122763954922 : (((p3 ∨ (p4 ∧ ((True ∨ (p4 ∧ (p4 → p3))) ∨ False))) ∧ (p3 ∧ (((False ∨ (False ∧ (p5 ∨ (p2 ∨ p4)))) ∨ False) ∨ p3))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185497137828371407879652534282 : ((p2 ∨ ((True → (p1 ∨ ((False ∧ False) ∧ True))) ∨ (p5 ∨ p5))) ∨ ((p5 ∧ (p5 ∨ p2)) ∨ ((p5 ∧ (p1 → (p5 ∧ (p2 ∧ False)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



