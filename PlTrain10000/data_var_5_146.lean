variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244826370365719181209919259693 : ((p1 ∧ p1) ∨ (((p4 ∨ p2) ∨ p4) ∨ ((p4 → (((True ∨ False) ∧ (True ∨ (p1 ∧ p4))) ∧ p4)) ∧ (p4 → ((p3 ∨ p5) ∨ (True → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62492593354389455303332281667 : ((p3 ∧ (True ∧ (True → ((p2 ∨ p5) → (((True ∨ (True → p5)) → (p4 ∨ ((p1 ∨ (p2 ∨ True)) ∨ (False → True)))) → (p4 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179201280279018297231080025896 : ((p3 ∧ (p5 ∨ (p4 → (True → (p5 → ((p4 → True) ∨ (False → p2))))))) ∨ (p5 ∨ ((p3 ∨ p5) → (True ∧ (((p1 → False) ∨ True) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312232031442288179644308800692 : (p2 ∨ (p1 → ((p3 ∨ (((((p3 ∨ ((p4 ∧ p1) ∧ True)) → p4) ∨ p3) → (p2 ∧ True)) → ((((p1 ∧ True) → p3) ∨ False) → p5))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256989318602464053503440183414 : ((p1 ∨ p5) → (p5 ∨ (((((p3 ∨ (((False → True) ∨ False) ∨ ((p5 → p5) ∧ (p2 ∧ p3)))) ∨ p2) → p2) ∨ True) ∨ (p3 → (p3 ∨ p3))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111776119706563966926582200358 : ((((((((True ∨ (((p5 ∨ p4) ∨ ((p1 → False) ∨ True)) ∨ (True ∨ p2))) ∨ p5) ∨ False) → p1) ∧ True) ∨ (p3 → True)) ∨ p2) ∨ (p4 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620118427712148985255398801773 : (((((False ∧ p2) ∨ ((p5 ∧ p3) ∨ ((p3 → ((p5 ∧ p5) ∨ p3)) ∨ (((((p4 ∨ p4) → p2) ∧ (p5 ∨ p5)) → True) ∧ p2)))) ∨ p2) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266261374077612982243684159365 : (True ∧ (p5 → (((((p3 ∨ True) ∧ (p3 ∨ p3)) ∨ (p4 ∧ p1)) ∧ (p5 → ((False ∨ p5) ∧ False))) → ((p2 ∨ p3) ∨ (False ∨ (p5 ∨ False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111972799890209198332481549048 : ((((p5 → ((p1 → (p2 ∨ False)) ∧ p2)) ∧ (((p1 ∧ p1) ∧ (p2 ∧ (p3 ∧ ((p4 ∧ p2) ∨ True)))) ∧ (False ∧ p1))) ∨ True) ∨ (False → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191572490922291996334161928496 : ((p2 ∧ (((False → (p2 ∨ p4)) ∨ (p1 ∨ p3)) → p4)) ∨ (False → ((True ∨ (p1 ∨ p1)) ∧ (p4 → ((p5 ∧ p2) ∨ (p5 → (p2 ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150340783366894194004106718910 : ((p5 → ((((p3 ∧ (((p1 ∧ p2) → (False → p2)) → (p4 ∧ True))) ∧ (p5 ∨ True)) → False) ∨ (False → False))) ∨ (p2 ∧ ((p1 ∨ p4) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618661201732063335865992879690 : ((((((False → p3) ∧ True) ∧ (((p2 ∨ p1) ∨ p4) ∨ (((p2 ∨ False) → (False ∨ p5)) ∧ (((p3 → p4) ∨ (p1 ∧ True)) ∨ p3)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_640083961266634146170000650243 : ((((((False ∨ False) ∧ True) → ((False ∧ (((p5 → (False → (p1 ∧ p4))) ∧ True) → ((True → p1) ∧ p1))) ∧ ((False ∧ p2) ∧ p1))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655060560941581126435347979595 : (((((p3 ∧ ((p5 ∨ (p2 ∨ (((p1 ∧ ((p2 ∨ False) → False)) → (((False ∨ True) → p2) ∧ p2)) ∨ p3))) → p1)) → False) ∨ (True → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58718587226692889489502209134 : (((p3 → False) ∧ (p1 ∧ (p4 ∧ ((True ∨ (p2 → (((p2 ∧ (False ∧ True)) → (p3 ∧ (True ∧ (p3 ∧ p4)))) → p4))) → (p2 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205914597802083522636106434331 : ((False ∧ (((p4 ∧ p2) ∧ p1) ∧ p5)) ∨ ((p2 → False) → ((p3 ∧ p1) → ((p1 → (p3 ∨ (False ∧ p3))) ∧ (p1 ∨ ((p4 ∨ True) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258997421739232471633433419142 : ((True → p3) → (p3 → (((p3 ∨ p4) → ((False ∧ (p3 ∨ ((p3 ∧ p5) ∨ ((True ∨ p2) ∨ (p3 ∧ p4))))) ∧ p4)) ∨ ((p3 → False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58837148851119836144402493767 : (((True ∧ False) ∨ (p1 ∨ (((((False ∧ p1) ∧ ((True → False) ∨ p2)) ∨ p3) ∧ ((p4 → p2) ∧ (p1 → ((p2 → False) ∨ p2)))) ∨ True))) ∨ False) := by
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
theorem thm_5_vars_50173803587753048680205788934 : ((((((p4 ∨ p3) → ((p3 ∧ p3) ∨ (((p5 ∨ (True ∧ p4)) ∨ False) ∧ (False → p2)))) ∨ False) ∧ p5) ∨ (((p1 ∧ p5) → True) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111360654048259947737294146167 : (((p5 ∧ ((((p3 → ((False → (p1 ∧ (True → True))) ∧ (p5 ∧ True))) ∨ p5) ∨ (p1 ∧ (p3 ∨ p2))) ∨ (p4 ∨ False))) ∧ p2) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587883130143572063831442345920 : (((((((True ∨ ((False ∧ (p5 ∧ p4)) ∧ False)) → (((p1 ∨ (p2 → False)) → ((p5 ∧ p2) ∧ p3)) ∧ p2)) → (p4 ∧ p5)) ∨ True) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185145875007790858640176965664 : (((False ∨ p2) → (p3 ∧ ((p3 ∧ p4) ∨ ((p5 ∧ False) ∧ p4)))) ∨ (((True ∧ p5) → (p5 → p2)) ∨ ((True → (p3 → False)) → (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320476973907706369358523388166 : (p4 ∨ ((p2 → p3) → ((((p4 ∨ ((((False → False) → p4) → (p3 ∧ (p3 ∨ True))) ∨ p4)) ∨ p4) ∧ p3) ∨ (p2 ∨ (False → (False → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230740356320490887176140157016 : (((p5 → p3) ∧ True) → (((((p4 ∧ p1) ∧ p3) → ((p1 ∨ p5) → (p3 → False))) ∨ True) ∨ ((p4 → p3) → ((p2 → (False ∨ False)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116220880543298116400693068430 : ((((p3 ∨ p1) ∨ False) ∨ (((True → (p3 ∧ False)) → (p1 ∨ ((((p4 → p1) → (True → (False ∨ p2))) ∨ p3) ∨ p3))) ∨ p4)) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697945080830523748792080755419 : (((((p4 ∧ ((p3 → ((p5 ∨ True) ∧ p4)) ∧ (p4 ∨ False))) ∧ p5) ∨ ((p3 ∨ (True ∨ True)) ∧ (False → ((False → (p5 → p3)) → False)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669894236046927014714498373200 : ((((((p3 ∨ (p5 → p3)) ∧ (((p2 ∧ (p1 → p5)) → p4) ∧ p4)) → ((p5 → ((p4 → p2) ∨ p4)) ∨ True)) ∨ (p3 → (p3 ∨ p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114643169579588124347530456298 : (((((p1 ∧ (False ∨ (((p1 ∨ False) ∧ (p5 → True)) ∨ False))) ∧ True) ∨ (False ∧ p4)) ∨ ((p4 → ((False ∨ p5) → True)) → p2)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345508700412354237992738471657 : (p3 → (((p4 → (((False ∨ (p3 ∨ True)) ∨ ((p4 ∧ p2) ∧ p3)) ∨ (False ∨ True))) ∧ ((p3 ∧ ((False ∧ p5) ∧ (p5 ∧ p1))) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738910998513264596504195741408 : ((((p3 ∧ False) ∨ (((p2 ∨ True) → (((p5 ∨ p5) → (p2 ∨ (True → True))) → True)) ∧ (p5 ∨ (((p1 ∧ (p5 ∨ p4)) → False) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725282418003427732389015853142 : ((((p3 → (False ∨ True)) ∧ ((((True ∨ p1) ∨ p4) → ((((p5 ∨ ((p2 ∧ p5) → p2)) → p4) → (p2 ∨ True)) → False)) ∨ (True ∨ p3))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676282956591497119432809862341 : (((((True ∧ (p3 ∨ p3)) → ((((p1 ∨ ((p3 → (p5 → (p5 ∧ True))) ∨ p5)) ∨ p5) ∧ False) ∧ p3)) ∧ ((False ∧ (False → p1)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346622506554663242376894820851 : (p3 → ((((p5 ∨ p1) ∨ False) ∨ ((((True ∧ p1) → (((p1 → False) ∧ p3) ∨ p1)) → p5) ∨ ((p3 ∧ False) → p3))) ∨ (p2 ∧ (p5 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_338613686155642943722676232050 : (p1 → ((False ∨ (p3 ∧ True)) → (((p1 ∧ (True → ((p3 ∧ p2) → (p2 → True)))) ∧ (((((p5 → p2) ∨ p2) ∨ p3) ∨ p3) → p5)) → p5))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : ((((p5 → p2) ∨ p2) ∨ p3) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54109865911398758679045700143 : (((p3 ∧ ((((False ∨ p4) → p2) ∧ (p3 → p4)) ∧ True)) → (p5 ∨ (p4 ∧ ((p2 ∨ True) ∨ (True → (True ∨ (p2 ∧ (p4 → p4)))))))) ∨ p4) := by
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328459396120775483668635751396 : (True → ((((p2 ∧ p4) ∨ False) ∨ ((p3 → ((p2 → True) ∧ p3)) ∨ ((p3 → (p3 ∨ p2)) ∨ p4))) → ((((p2 → p3) → p4) ∨ True) ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
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
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353699773860994107521661912267 : (p4 → (p5 ∨ (p3 ∨ ((p3 ∨ (p2 ∧ ((p4 → (((p5 ∧ (p5 ∨ p1)) ∧ p3) ∨ (p5 → False))) → p1))) ∨ ((p4 ∧ (True ∨ p3)) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321561984301002367508109447683 : (p4 ∨ (p2 → ((((p4 → (p1 ∧ p2)) ∧ p3) → p1) ∨ (((((p4 → (p5 ∧ (p5 → p2))) → p1) → p5) → (p5 → (p5 ∧ True))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158894713417001364222476256711 : ((p1 ∨ (((p2 ∧ (p2 → (True → ((p2 ∨ p1) ∨ (((p4 ∨ True) ∨ p1) ∨ p4))))) → False) ∨ True)) ∨ (p3 → (p4 → (True ∧ (True → True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118558241400833781154435295061 : ((p3 ∨ (p4 → ((p1 ∧ p1) ∨ (((p5 ∧ (False ∨ ((False ∨ (p5 ∧ (p3 ∧ p4))) ∨ p3))) ∨ True) ∨ (p4 → (False ∧ p1)))))) ∨ (True → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_116048607329987159110025954516 : (((p1 → (p1 ∧ (True ∨ True))) → ((p3 ∨ ((p2 ∧ (p3 → p1)) ∨ p4)) ∨ (p4 → ((False → ((True ∧ p2) ∨ p5)) ∨ False)))) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169034334546500336761618637685 : ((p2 → ((p3 → (p1 ∧ (True ∨ ((p1 ∧ (p1 ∧ True)) → p5)))) → ((p2 ∧ p3) → p5))) → ((p5 ∨ True) ∨ (p3 ∧ ((False ∧ p3) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114797176528865093924565322516 : ((((p4 ∧ ((p4 ∧ (p1 ∧ p1)) ∨ (p3 → p4))) ∧ (False → (p3 ∧ True))) ∧ (((p1 ∨ True) ∨ (p3 ∧ p1)) ∧ (p3 ∨ True))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684843723544316456546776444290 : (((((p1 → True) → ((p1 → True) → (((p2 → p5) ∧ True) → ((p5 → (p2 ∨ p3)) ∧ p4)))) ∨ (((True → (False ∧ p4)) → p5) ∨ p3)) ∨ p3) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230936560157090618950717182535 : (((p3 ∧ p2) ∨ p5) → ((p5 → p5) → (((p1 ∧ (((p3 ∨ True) ∧ p3) → (p4 → ((False → p2) ∧ (p5 → False))))) ∨ (True ∨ p4)) ∨ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201094380291256814046432038254 : ((True → (((p3 ∨ (True ∧ False)) → p5) ∧ True)) → (((((False → ((True ∧ p4) → False)) → (True ∧ (p5 ∨ True))) → p4) ∨ False) → (p2 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((False → ((True ∧ p4) → False)) → (True ∧ (p5 ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317880968984276891669891693721 : (p4 ∨ ((True ∧ ((((p2 ∧ ((True → True) ∨ (p2 ∨ ((True → p2) → (p2 ∨ (p1 ∧ True)))))) ∨ ((p3 → False) ∧ True)) → p1) ∨ True)) ∨ p1)) := by
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
theorem thm_5_vars_52829591396060264636965167018 : (((((p2 ∧ False) ∨ True) ∨ (((p2 ∨ (False ∨ p2)) ∧ (p2 ∨ p3)) ∧ p5)) → ((True → ((p1 → False) → ((p2 ∨ p3) ∧ p3))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316490087647917230419006509371 : (p3 ∨ (p2 ∨ ((p2 ∧ ((((p5 ∧ ((p3 → False) ∨ (p4 → False))) ∨ (p1 ∨ (p4 ∧ (p5 ∨ p2)))) → (False ∨ p3)) ∧ (False → False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147798463991856754149019375506 : (((p1 ∧ (((p2 → ((((p5 → p5) ∨ p5) ∨ True) ∨ ((p2 → True) ∨ True))) ∨ (p3 → p5)) → p1)) → p5) ∨ (((p2 → False) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165653685721170254443072218471 : (((((p5 → p2) ∨ (True → p2)) → p3) ∨ (((False → p5) ∨ p2) ∧ ((p5 ∨ p4) ∨ True))) ∨ (p1 ∨ (False → (p4 ∨ ((p1 → p3) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39907431591630810802330226148 : (((p3 → ((((p5 ∧ (((p1 ∧ p3) → ((p1 → p2) ∨ p1)) ∧ p4)) → ((p4 ∧ ((p2 → p5) → False)) ∨ True)) ∧ True) ∨ p4)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138161619290585179734711968135 : ((p1 → ((((False ∧ False) ∨ (p5 ∧ (p5 ∨ ((True → (((p3 ∧ p4) ∧ p5) ∧ p4)) → False)))) → p1) → (p3 → p3))) ∨ (p5 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215753710208377407112551480997 : ((p1 ∨ ((False → True) ∧ False)) ∨ (p2 → ((p5 → ((p3 ∧ (p1 ∨ True)) ∧ (True ∧ p2))) ∨ (p3 ∨ (((p1 ∨ p1) → (p5 ∧ True)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656184006072625663469843842948 : (((((p5 ∧ ((p2 ∧ (((p3 ∨ False) → (False → p3)) → False)) ∧ (p4 ∧ p1))) ∨ ((p2 ∨ ((p2 ∨ p2) → True)) ∨ p3)) ∨ (p3 ∨ False)) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352798960922604573496690137450 : (p4 → ((p2 ∨ p3) → (((((True → (p3 ∨ (p5 → ((p5 → True) ∨ p3)))) → p2) ∨ p3) ∨ False) ∧ ((p5 ∨ (p1 ∧ False)) ∨ (p4 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186515683669295587033592317504 : ((((((p2 ∨ p4) → p2) ∨ (p5 → p1)) ∧ True) ∨ (p1 ∧ p3)) → (p1 → (p3 ∨ (((p5 ∧ p4) → (False ∨ ((p3 ∧ p4) → p3))) → p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675000366347917899292981251414 : ((((((p1 ∨ True) ∨ ((p4 ∨ p4) ∧ (p2 ∧ ((p4 ∨ p1) ∨ (True ∧ ((p4 ∧ p1) ∧ False)))))) ∧ True) ∧ (False ∨ ((p2 ∨ p1) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797285795288405414647204374 : ((True ∧ ((False ∧ False) ∧ (((((True ∨ ((((p1 ∨ False) ∧ p2) ∨ (p4 ∧ (True ∧ p4))) ∧ p4)) ∨ False) → p4) ∨ p4) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357018774499200289527928747823 : (p5 → (((p4 ∧ p3) → p1) ∨ ((((p2 ∨ (p3 ∨ p3)) ∧ (((p5 ∨ ((True ∨ (p5 ∧ p5)) ∧ p1)) → p4) ∨ p2)) ∨ (False → p2)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61264764511417350841977820332 : ((False ∧ (p1 ∨ ((((((((p5 → p4) ∧ p1) ∧ (p5 → ((p2 ∧ p1) → True))) → p5) → p4) → p1) → False) ∧ (p2 ∨ (p3 → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190916010837050758563533707800 : (((((p4 ∧ p2) ∨ False) ∧ p4) ∧ (False ∧ (p1 ∨ p2))) ∨ ((p3 ∧ (((p4 ∧ p4) → p2) ∨ (p5 → p3))) ∨ ((p2 ∧ p5) → (True → True)))) := by
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
theorem thm_5_vars_305040026741820424707782407940 : (p1 ∨ ((p5 → ((((p4 → (((p4 → ((True ∨ p1) → p4)) ∨ p2) → (p2 ∧ p2))) ∧ False) ∨ (p2 ∨ True)) ∧ False)) ∨ (p2 ∨ (p3 → p3)))) := by
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
theorem thm_5_vars_338268251072269308886816195958 : (p1 → (((((False ∨ True) → p5) → p1) → False) → (p5 → (p4 ∨ (p2 ∧ (p3 → ((p5 ∨ (p1 ∨ True)) ∧ (((p2 ∨ p4) ∨ False) ∧ True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∨ True) → p5) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171899631863790107326421152046 : (((p5 ∨ ((False ∨ (((True ∧ False) ∧ p4) ∨ p2)) ∧ (p3 ∨ (p4 ∧ p5)))) → p5) ∨ (p5 ∨ ((p1 ∧ (((p2 ∧ True) ∨ p4) ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789921985148518713304946791029 : (((p5 ∨ ((p2 → (p3 ∧ p1)) → ((((p5 → p5) ∨ p4) → p4) → ((((((True ∧ p2) ∨ p1) ∨ True) → p2) → (p5 ∨ p5)) → p4)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → p5) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652958388877879790514708046 : (((((((p4 → True) → p4) ∨ ((p2 ∨ p1) ∧ p1)) ∧ (True → p4)) ∨ (((p5 ∧ p2) → True) ∧ p1)) → (p2 ∨ (p5 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668913251569993778632200286972 : (((((p2 ∧ ((p4 ∨ p4) → (p2 ∧ ((False → p2) ∧ ((p5 ∧ p4) ∨ (p5 → (True ∨ (p5 → p2)))))))) ∨ False) ∨ ((p3 ∨ p5) → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63370519029134014175662153179 : ((p5 ∧ (p4 ∧ (p1 ∨ ((((p1 ∨ p5) ∧ ((p1 ∨ (False ∧ False)) ∧ p1)) → (p1 → (False ∨ (p2 → (p1 ∨ p1))))) ∧ (p1 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305135398575318027264758634733 : (p1 ∨ (((True ∧ (p3 ∨ p2)) ∨ ((True → (((p1 ∨ False) → ((p1 ∨ p2) → True)) ∧ (False ∧ p2))) → p4)) ∧ (((True → False) → p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655177164712986941531244052293 : (((((p5 → ((((p2 → p2) ∨ ((True ∨ p5) → ((True → (p1 → (True → False))) → p2))) → p3) ∨ (p1 → p4))) → False) ∨ (p1 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_172515849804020556802947180405 : ((((p4 ∨ p1) → False) ∧ (p2 → (((False ∨ p4) ∨ ((p5 → p4) ∨ p1)) ∧ p3))) ∨ ((((p2 → (p3 ∧ p5)) → p2) ∧ (p1 ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336294287440957142812038503936 : (p1 → (((((True ∧ (p5 ∧ True)) → (p5 ∨ True)) → False) → (p4 ∨ (p3 ∨ ((p3 ∨ (True → p2)) ∧ ((p5 ∧ (p2 ∧ p5)) ∨ p1))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∧ (p5 ∧ True)) → (p5 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701711421734607251522210225542 : ((((True ∧ (((p2 ∨ (p4 → p1)) ∧ p3) → (p2 → False))) ∧ ((((((p5 ∧ (False ∨ p2)) → False) → (p5 ∧ p1)) ∨ p3) → p2) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48376666280391282760997575796 : (((True → ((p5 ∧ ((p1 ∨ (p4 ∧ p1)) ∧ ((p3 ∨ ((True ∨ p3) ∨ ((False ∨ p5) ∨ p2))) ∧ (False ∧ False)))) ∧ True)) → (p2 → False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137911370814880054618114728737 : ((p4 ∨ ((((True → True) ∨ p4) → p5) ∧ ((((p4 ∧ p2) ∨ p2) → ((p4 → True) ∧ (p4 ∧ p3))) → (p3 → p4)))) ∨ (False → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591558005050086768366651312110 : (((((p5 ∨ ((p4 → p3) ∨ (((False ∧ ((p2 → (p2 → (True ∨ (p1 → (p4 ∧ p4))))) → False)) ∨ True) ∨ p4))) ∧ (True ∨ p4)) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196724199782791937334527720307 : (((((p2 ∧ p4) → (p4 ∧ True)) → p1) ∧ p3) ∨ ((p4 ∨ (((p1 → False) ∨ True) ∨ ((p1 ∧ ((False → p3) ∨ p3)) ∧ True))) ∨ (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_322364050241616267953150767566 : (p5 ∨ ((((p4 → False) ∧ (((False → ((p3 → (p2 → False)) ∨ (True ∨ True))) → (p3 ∧ p4)) ∨ (p3 ∨ p1))) → ((True ∧ p4) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257691990174794204222549261598 : ((p3 ∨ p3) → ((p4 ∧ ((((p1 ∨ p4) ∨ (((p1 ∧ p4) ∧ p4) ∨ p2)) → p2) ∧ p1)) ∨ (p5 → ((p4 → p5) ∧ ((True ∧ p4) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164929035886631800379625421377 : (((((False ∨ ((False → False) → p5)) ∨ (p5 ∧ (False ∧ ((p5 ∧ p2) ∧ p1)))) ∨ True) → False) ∨ ((p4 ∨ False) ∨ (p4 ∨ ((p3 ∧ False) → p5)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61530945487928364044042822852 : ((p1 ∧ (((((p1 → p5) ∧ (p4 → (((p5 ∧ p4) ∧ p5) ∧ p2))) ∨ p3) ∨ p1) → ((p4 → p4) → (p4 ∧ (p1 ∨ (p2 ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117357120823154528323727802653 : ((False ∧ (p5 ∧ (p4 ∧ (p4 ∧ (((((p1 ∨ (True ∧ (p5 → p1))) ∨ ((p4 → p5) → (p1 → p4))) → p5) → p3) ∧ p1))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695938716001545689909121543560 : (((((p3 ∨ p5) → (((p3 ∧ p4) → ((p4 ∨ (p1 ∧ False)) ∨ True)) ∧ p1)) → (((p4 ∧ True) ∨ (((p5 ∧ p3) → p3) → p3)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113345873145787744294902462213 : (((False ∧ (((False → ((True → (False ∧ ((p2 → ((True ∧ p2) ∧ p1)) ∧ p5))) ∧ p3)) ∨ p2) → (False ∨ p5))) ∧ (p3 ∧ p4)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94826295505853506907206893538 : ((p3 ∧ ((p5 → False) ∧ ((((p4 → ((False ∨ (p1 ∨ p5)) ∧ ((True → p1) ∧ (p4 → True)))) ∨ ((p5 ∨ False) → False)) ∨ False) → False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 → ((False ∨ (p1 ∨ p5)) ∧ ((True → p1) ∧ (p4 → True)))) ∨ ((p5 ∨ False) → False)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h6
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754507127763261902958024143033 : (((False ∧ (False ∧ ((p3 ∧ ((False ∧ True) → ((p2 ∨ (p5 ∧ False)) ∧ p3))) ∧ (p3 → ((p5 ∨ p2) ∧ ((p3 → (p1 → p3)) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356780867092904802322703371847 : (p5 → ((p2 ∨ ((p4 ∨ p3) → (p4 ∧ p2))) → (((p5 → p1) → ((p4 → ((p1 ∨ p5) ∨ p3)) → (p4 ∧ p4))) ∨ ((False ∨ True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9917581736701536734799952913 : (((p1 ∧ (False ∧ (p1 → (((p4 ∨ (((((p1 ∨ (p2 ∧ True)) ∨ p3) ∧ False) ∨ (p1 ∨ (False ∨ True))) ∨ p1)) → p3) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61485262191986333877548692313 : ((p1 ∧ (((p2 ∨ (p3 ∧ True)) → (((p4 → (True ∧ False)) ∨ p1) ∧ (p2 ∧ ((p3 ∧ p1) ∧ (p3 ∨ True))))) ∧ ((p2 ∧ p3) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2372790753243925888683915560 : (((((p4 ∨ p1) ∧ p1) ∧ p1) ∨ (p4 ∧ (p1 ∧ (p5 → p1)))) ∨ ((((False ∨ p3) ∨ p2) ∨ (p1 ∧ (p2 ∨ (p5 ∧ p3)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137452024183755282594066028225 : ((p4 ∧ (((p1 → True) → p4) ∨ ((p3 ∨ p1) → (p5 ∧ (p2 ∧ (((p3 ∧ p3) ∨ ((p4 ∧ False) → p3)) → p4)))))) ∨ ((True ∨ p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41586742814559415660607344230 : (((((p4 ∧ True) → (p5 ∧ (p4 → (p5 → p3)))) ∧ (p2 ∧ (((((p5 → (p4 ∨ p1)) → p1) → p2) ∧ (p4 ∨ False)) ∨ p1))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97321883923037311519864542397 : ((p2 ∨ ((((p4 ∨ True) ∨ False) ∨ ((p2 → p4) → True)) → (((p1 ∨ (False ∧ p3)) ∨ ((p3 ∨ True) → (True → (p5 ∨ False)))) ∧ False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p4 ∨ True) ∨ False) ∨ ((p2 → p4) → True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691070906197058859217973994550 : ((((((((((True ∨ p3) ∧ p2) → p4) ∧ p2) → p2) → p1) → ((p4 ∨ p1) ∧ p2)) → (p1 → ((((p1 ∧ True) → p2) ∨ p4) ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((((((True ∨ p3) ∧ p2) → p4) ∧ p2) → p2) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148426250615885594951011401756 : (((((p3 → p2) ∨ p3) ∧ (True ∧ (p3 → ((p1 → (True ∨ p4)) ∧ True)))) → (p2 → (p2 → (p4 → p2)))) ∨ ((True ∧ (p4 ∧ False)) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354863859338488778567975731157 : (p5 → (((p4 → p1) → (False ∧ ((p2 ∨ False) ∨ (((p4 → ((p3 ∨ (False → p5)) ∧ p3)) ∧ (False ∧ ((p3 ∨ p3) ∧ True))) ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65711421199520339027443504029 : ((p4 ∨ (((p5 → (((False ∧ (p1 ∧ p5)) → p4) → ((True ∧ (((False ∨ False) → (p5 → False)) ∧ False)) ∧ p2))) ∧ True) ∨ (p4 ∨ True))) ∨ p1) := by
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
theorem thm_5_vars_797554880486390932676623273764 : (((p1 → ((((p1 → False) ∧ ((True → (p2 ∨ ((p1 ∧ (((False ∨ (False ∧ True)) ∧ (False ∨ p3)) ∨ p2)) ∧ p1))) ∧ p4)) → p5) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337679152300835549517734697465 : (p1 → ((p5 ∨ (((((p1 ∨ (True ∧ False)) → ((False ∨ p1) ∨ (False → p2))) ∧ p1) → p5) ∧ p4)) ∨ ((True ∧ (p3 ∧ (False ∧ p3))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



