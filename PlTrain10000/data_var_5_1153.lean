variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620709482775507094731082263075 : (((((p2 ∧ p2) → ((((p3 ∨ p5) ∧ False) ∨ p4) ∧ (((p2 ∧ ((True → (True ∧ ((p1 ∨ True) ∧ True))) ∧ p4)) → p5) → p5))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_695239808087579670806260422640 : (((((((True → (((p4 ∨ p1) ∨ True) ∨ (True ∧ p2))) ∧ p5) ∨ False) → True) → ((((False ∨ (p1 → False)) ∨ p5) → p5) ∨ (True ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690188840939267373083346704164 : ((((p3 ∨ (((p1 ∧ p3) ∨ True) → ((((p4 ∨ p1) ∨ (p5 ∨ p1)) → p4) → p2))) ∨ ((p4 → p2) ∧ ((p1 ∨ (p2 ∧ p1)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678243264859947996128822609966 : ((((((p4 ∨ (p1 ∨ p3)) ∧ (((p1 → p4) ∧ True) → p3)) → (p4 ∨ ((p4 → (p5 ∧ p1)) → p2))) ∨ ((True ∧ (p4 ∨ True)) → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_159785593240644406205084064619 : ((((p4 → p1) → (((((True ∨ (p3 ∨ p3)) ∧ (True → p5)) ∧ p5) ∧ (p3 ∧ p2)) → p4)) ∨ False) → ((p1 ∧ (p4 → (p5 → False))) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673825241679188825556817464978 : (((((True → p2) ∨ ((p4 → ((p3 ∨ p2) ∧ p5)) ∧ ((((p5 → (True ∨ False)) ∧ True) ∨ (True ∨ p5)) → p3))) → ((p1 ∧ False) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325793168893344367460183564101 : (p5 ∨ (p3 ∨ ((((((p3 ∧ (p4 ∧ p3)) ∨ False) ∨ (p4 ∨ (p5 → (p1 ∧ ((((False ∧ False) → p4) ∨ p3) ∨ False))))) ∧ p3) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321534078378187611874551278409 : (p4 ∨ (p2 → (((((p1 → p3) ∧ ((False → (p3 ∨ (False ∧ (True ∧ p1)))) ∨ (p1 → (((p3 ∨ False) ∨ p1) ∨ p2)))) → p1) ∧ False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148506993706960490758613982787 : (((p5 ∨ (((p5 ∨ False) ∨ ((p3 ∨ p5) ∧ (False → True))) → p1)) ∨ ((p4 ∨ p2) ∨ ((p4 → False) → p5))) ∨ (((p3 → p5) ∧ p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430429608680567329238969745244 : ((((((p3 ∧ (p1 ∨ True)) ∨ p2) → (p5 → ((((p5 ∧ False) ∧ p1) ∧ (p1 ∧ False)) ∨ ((p4 ∨ (p5 ∧ p3)) ∧ p4)))) ∨ (p1 ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_311272212304109378127837364391 : (p2 ∨ (True ∧ ((p5 ∨ (((p4 → ((((p5 ∨ p5) ∧ p4) → p3) ∨ (True ∧ ((p2 ∧ p2) ∨ p2)))) → p3) ∨ True)) ∧ ((False ∧ False) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768028512680993017267115645462 : (((p5 ∧ ((((((False ∧ (p2 ∧ False)) → (False ∧ p5)) → (((p5 ∨ p1) → (False → p3)) ∨ p2)) ∧ p2) ∨ (p5 ∨ p1)) ∧ (False ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244208557363968403068300528454 : ((True ∧ p5) ∨ ((p3 ∧ ((p2 ∧ ((((p2 ∧ p1) → p5) ∧ ((p2 ∨ True) ∧ p5)) ∧ False)) ∧ False)) ∨ (((p1 ∧ (False → True)) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598799760342658543644203011028 : (((((p2 ∧ p2) ∧ (False ∧ ((((p1 ∧ ((False ∨ (p1 → p4)) ∨ p2)) → (p3 ∨ ((p5 ∨ p4) ∧ (p5 ∨ False)))) ∨ True) → p4))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196913223137553610445373165561 : (((((p3 ∧ (False ∨ False)) ∨ p4) ∧ p3) ∨ p4) ∨ ((p2 ∧ False) ∨ ((p3 ∨ True) ∨ ((((p4 → (p5 ∧ True)) ∨ True) ∧ True) → (p1 → p3))))) := by
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
theorem thm_5_vars_50487577402072991743797720191 : (((p4 → (((p5 → False) ∨ (p3 ∧ (False ∧ (p3 ∨ (p3 → ((p1 ∧ (p4 ∧ p5)) ∧ False)))))) ∨ p4)) ∨ (p2 ∧ ((p3 ∧ False) ∨ p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768220828788276381930977048057 : (((p5 ∧ ((p5 ∧ ((((p3 → (False ∧ p3)) ∨ (p5 ∨ p4)) → ((True ∧ p1) ∨ (p1 ∧ p2))) → ((p4 ∨ p5) ∨ p3))) → (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205552775662089658805213858997 : (((p4 ∨ p2) ∧ ((True ∨ p2) ∨ p4)) ∨ (((p3 → False) ∧ (True ∧ p5)) ∨ (p4 ∨ (False ∨ ((p2 ∨ (((p4 ∧ p3) → True) → p4)) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184132293051299362321432766914 : (((p2 ∧ (((p1 → p4) ∧ p1) → (True ∨ (p5 → False)))) ∨ False) ∨ (p2 ∨ (p4 ∨ (((False → p2) ∧ ((True ∨ p5) ∧ p4)) → (p1 ∨ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166241628312845659917306390205 : ((p2 ∧ (p1 → (True → ((((p4 ∨ p5) ∨ True) ∧ (p5 ∧ ((p5 ∨ p5) ∧ False))) ∧ p1)))) ∨ (((p1 ∧ p1) → p1) ∨ ((p4 → p2) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701080600949565089790916950053 : ((((((True ∨ (p4 → (p2 → p1))) → (p3 ∧ True)) → p2) ∧ (((p4 ∧ (p3 ∧ (p5 ∧ p2))) → p5) → ((False ∧ p3) ∧ (True ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52022537485777394407481536771 : (((False ∨ (((p3 ∨ p2) → p2) ∧ ((p3 → (p1 ∨ ((p1 ∨ p5) → p1))) ∨ p2))) ∨ ((((p2 → p3) → (True ∧ True)) ∧ False) → p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_219047869024263401352718386006 : ((p5 ∧ ((p4 ∨ p4) → True)) → (((p5 → p5) ∨ p4) → ((True ∧ p2) → ((((p1 ∨ ((p5 → (False → p3)) ∨ False)) → p4) ∧ False) ∨ p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315854058542855470215489217364 : (p3 ∨ ((p2 → p3) → (((p4 → p5) ∨ (p4 → False)) ∨ (((False → (True ∨ p2)) ∧ p5) ∨ (p5 → (p5 ∨ (p4 ∨ (True ∧ (p2 → p1))))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62940322886653624311911029032 : ((p4 ∧ (p3 ∧ (p1 → (((p1 ∧ p1) ∧ ((True ∧ ((p2 ∧ p2) ∨ p2)) → (p5 ∧ (p4 ∨ p4)))) ∨ (((True ∧ True) ∧ p1) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345630528958496503029998369883 : (p3 → ((p1 ∧ ((((((p5 ∧ ((True ∨ p2) ∨ (p2 ∨ (True → (p3 → p1))))) ∨ True) → (p3 ∧ p5)) ∧ p1) ∧ (p2 ∧ p2)) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224328126771627070015318340314 : ((False → (p3 ∨ p4)) ∧ (((False ∧ (p3 ∨ (p1 ∨ ((p2 ∨ p3) → p2)))) ∧ (p3 → (False ∨ ((p3 ∨ False) ∨ (p5 ∧ (p2 ∨ p1)))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304845637198244930205111091850 : (p1 ∨ (((((((p5 → p1) ∧ p5) ∧ (p2 → p3)) ∧ p2) ∧ (p1 ∨ p2)) ∧ ((False ∨ ((True ∧ p2) ∨ (p4 ∨ False))) → False)) → (p4 ∨ p3))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h13 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h16 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h17 := h9 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133726906467086119566049396785 : (((((((False ∧ p2) → p1) ∨ True) → ((p2 → (p5 ∧ False)) ∧ True)) → ((p5 ∨ ((p4 → p3) ∨ True)) ∨ True)) ∧ p5) ∨ ((p2 ∧ p4) → p2)) := by
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
theorem thm_5_vars_765835810824686758809987706806 : (((p4 ∧ (((False → p3) → ((p4 ∧ False) → p3)) ∧ (((p2 → True) ∨ False) ∧ (True ∧ ((((p1 → p5) → p2) → p5) → (p4 → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349032274893866519726713101989 : (p3 → (p5 ∨ (((p5 ∨ ((True ∧ p5) ∧ ((p5 ∧ p2) ∧ p5))) ∨ ((((p2 ∧ ((True ∧ p1) ∧ (p4 → p4))) ∨ p2) ∨ p5) → p2)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347223272164833947425513232507 : (p3 → (((p2 ∧ ((False ∨ (p3 ∧ (p4 ∧ True))) → True)) ∨ (p1 → p2)) → (((p5 → p5) ∧ (((p1 → p5) ∧ p2) → p1)) ∨ (p4 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107051075048270536656767918190 : (((((True ∨ p1) ∨ p2) ∨ p1) → (p2 → (((((p5 → p2) ∨ p1) → p1) ∨ False) ∨ (True ∨ ((p4 → (True ∧ False)) ∧ p2))))) ∧ (p3 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355939646383385206139754985529 : (p5 → (((p1 → True) ∨ (((((False → (p5 ∧ ((p2 ∧ (p4 ∧ p5)) ∨ False))) ∧ p2) → (p1 ∨ p4)) ∨ p5) ∨ p2)) → (p2 ∨ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786143557696052078816689818212 : (((p4 ∨ ((((p2 ∨ ((((((p2 ∧ p5) ∧ False) ∨ p4) ∧ (p3 ∧ (True → True))) ∨ p5) ∧ p4)) → p1) → p3) ∨ (True ∨ (p2 → p2)))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203970933154357589619662245465 : ((p3 → ((False ∧ (p5 ∧ True)) ∨ p3)) ∧ (((True ∧ (p3 ∧ (((p5 ∨ p3) ∨ p2) ∧ p5))) ∨ (True ∨ p1)) ∨ (p4 ∨ ((p5 ∨ p4) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811453324846739458601598881042 : (((p5 → (p3 ∨ (False ∨ (((p1 ∧ ((((p4 ∧ (p2 ∧ p1)) ∨ (p3 ∧ p2)) ∨ False) → p1)) ∨ ((p4 ∨ True) ∨ False)) ∧ (p4 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113006590677004662075094291600 : (((p4 ∧ ((p4 → p1) ∧ (((p2 ∨ ((p4 → (p2 → (True ∧ ((p1 ∧ p3) ∧ True)))) → (p2 → p5))) ∨ True) → p4))) → False) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642231988148919976586882935860 : ((((True ∧ (p3 ∨ (p4 → ((((p5 ∨ p4) ∧ p5) → (p5 ∧ p5)) → (p3 → (p3 ∧ (True → (p4 → (p1 ∨ (p3 ∧ p2)))))))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247409775521144656853895981316 : ((False ∨ p2) ∨ (((True → True) → (((p3 ∧ ((((p1 → ((p2 ∧ p5) → (p3 → True))) ∨ p1) → p5) ∨ p5)) → p4) → (p2 ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351832404629555888271625333358 : (p4 → ((p5 ∨ (((p5 → ((p3 ∨ p3) → True)) → p1) ∨ (p2 → p2))) ∨ (((p2 → ((p5 ∨ True) ∧ (False → False))) → (p3 → True)) ∧ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158146298880410125824335268973 : (((True ∧ ((p3 → p1) ∨ p1)) ∨ (p3 ∧ (((p4 ∨ (p3 ∨ ((False → p1) → p1))) → p3) ∧ p3))) ∨ (p4 ∨ (((True → True) ∨ p2) ∨ p3))) := by
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
theorem thm_5_vars_234627134732582051676541424852 : ((p3 → (p1 → False)) → (p3 → (p1 ∨ ((p1 → (((((p4 ∨ ((p1 ∨ p5) ∨ p2)) ∧ p2) ∨ (p1 ∨ True)) → p2) → p4)) ∧ (p3 → p3))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48983338786449467468412070933 : (((((((p1 ∨ True) → p1) ∧ p4) ∧ (p5 ∨ (((False ∨ p2) → ((p2 → (p3 ∨ False)) → p3)) ∧ False))) ∨ p3) ∨ (p2 → (p4 → p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668324428824182261714439119459 : ((((p4 → (p1 ∨ (True → ((((p4 → (p3 ∨ (p3 ∨ False))) ∧ p1) → (False ∧ False)) ∧ (p2 ∧ (False → p4)))))) ∧ (p1 → (False ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140612442926795451028422860756 : (((((p3 ∧ True) ∨ (p4 → p2)) ∨ (((((p3 → p2) → p3) ∧ p3) → p5) ∧ p1)) → (p1 → ((p3 ∨ False) → p5))) → (p2 ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157249576329189373118023847822 : (((((p1 ∧ (False ∧ (p1 ∧ True))) → p2) ∨ (((p4 ∧ False) → (p2 → p3)) ∧ (False ∨ p3))) → p1) ∨ (False → (p5 → (p3 ∧ (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52401327074617103994248057528 : ((((((p3 ∨ True) ∨ p1) ∧ p1) → ((False ∨ ((p1 ∨ False) ∨ True)) ∧ p5)) ∧ ((p1 ∧ (p5 ∨ (((p1 → p3) ∧ p5) ∨ p3))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108275708880152716265981980194 : ((True ∧ ((((p1 ∨ p1) ∧ (p3 → (p3 ∧ (p3 ∨ p1)))) ∨ p4) → (p3 → (p5 ∨ (p2 ∨ ((p4 ∨ (False ∧ p1)) → p4)))))) ∧ (p5 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h16
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
  -- Implications on the right can always be decomposed.
  intro h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338515631437562616246441586123 : (p1 → (((p4 ∧ p4) ∨ False) ∨ ((((p4 → ((p3 ∧ (p1 ∧ ((p3 ∧ True) → True))) ∨ p4)) ∧ p1) ∨ (True ∧ p1)) → (False ∨ (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173107635285461453403791686338 : ((p2 ∨ ((((True → ((p1 ∧ p1) ∧ (p1 → False))) ∨ (p1 ∨ p5)) ∧ False) ∨ p5)) ∨ (((p2 ∨ (p2 ∧ False)) → p4) → ((False ∧ True) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119241670669914850940634073168 : ((p2 → (p2 ∧ (False ∧ ((((((((p2 → (p4 → (p4 → True))) → True) ∨ p1) → p1) ∨ p1) ∧ p1) ∧ p5) ∨ (p2 ∨ True))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756638153117949467628493925919 : (((p1 ∧ ((((p5 ∧ (p4 ∧ (p2 ∧ (False → (p5 ∨ p5))))) ∧ (p2 → p4)) → p3) ∧ ((((False ∨ p2) → False) → p4) ∨ (p5 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392270008074232105175991127474 : (((((p2 ∧ (p3 ∧ False)) ∧ ((((((p1 ∨ p5) ∧ False) ∧ ((p5 → True) ∧ (p1 ∧ (p5 ∨ p4)))) ∨ p4) ∧ p1) ∨ (p4 ∨ p5))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_45568615746687543175815916039 : (((p2 ∨ (True ∧ (((p1 → (((p3 → (p5 ∧ p2)) ∧ ((p1 ∧ p4) ∧ True)) ∧ (p5 → p4))) → (p1 ∧ (p4 ∧ p4))) ∨ p3))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38060376619827489815804102116 : ((((((False ∧ ((True ∧ ((p2 ∧ p3) ∨ (p3 → (p2 ∨ p1)))) ∨ False)) ∨ p2) → (p5 ∧ (False ∨ (p3 → p1)))) → (p5 ∧ p5)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116827745828579422474830548003 : (((p5 ∨ p1) ∨ (((p1 ∧ p4) ∧ (p5 ∧ p2)) ∨ ((((True → (((False ∧ p5) ∧ (False → p1)) → p1)) ∨ p2) ∧ p2) ∧ True))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219616150489407529742775775605 : ((False → ((p2 ∧ p2) ∧ p3)) → (p3 → (p3 → ((((((True → p1) ∨ (p5 ∨ True)) ∧ ((True → p4) ∨ p1)) ∧ p4) ∨ p2) ∨ (True → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47235839380281058940221892453 : ((((p3 → (((p4 ∨ (False ∧ True)) ∨ p2) ∨ p5)) ∨ (False ∧ ((p2 → p1) → ((p5 → ((p3 ∨ p2) ∧ p3)) ∧ p4)))) ∨ (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114204574920825742634626956423 : ((((p1 → (p5 → (p5 ∧ p4))) ∧ (((p4 → p5) → p3) → ((True ∧ p3) → (False ∧ (False ∨ p1))))) → (p3 → (p1 → p3))) ∨ (p4 → False)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300805691911461677583079252060 : (False ∨ (((((False ∨ (True ∧ (p5 ∧ (True → p5)))) → p1) ∨ (p3 ∨ (True → False))) ∨ p1) → ((p2 ∨ True) ∨ ((True → p1) ∧ (p3 → True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65365249983832281264134375224 : ((p3 ∨ ((p2 ∨ (((p3 ∧ ((p1 ∧ (True ∧ False)) → True)) ∨ False) ∨ p2)) ∨ ((p5 ∧ (((p2 ∧ (False ∧ p5)) ∧ p1) ∨ p2)) → p5))) ∨ p5) := by
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
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51109241787665351560742805634 : ((((p4 → (p2 ∧ ((p3 → ((True → ((True ∧ p1) → p1)) ∧ (p4 ∨ True))) → p2))) ∧ p3) ∨ ((True ∧ (p1 ∨ False)) ∨ (p1 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586026906428931769655610274938 : (((((((p2 ∨ p1) → ((((p4 → (p1 → (p5 ∧ p4))) → (p2 ∨ p2)) ∨ (p5 → p2)) ∧ True)) ∨ ((False ∨ True) ∨ p3)) ∧ p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46066202408974703306509887890 : ((((((False → (((p3 ∧ p1) ∨ True) ∧ ((p3 → ((((p1 ∧ p3) ∧ p3) → False) ∨ p5)) → p2))) ∨ False) → False) ∨ p4) ∧ (p1 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66138957359783868273258221576 : ((p5 ∨ ((((True ∧ (True ∧ (p1 ∨ (p4 → ((((False → (False ∧ p2)) ∨ False) → p5) ∧ p4))))) ∨ p5) ∨ (False ∨ p4)) ∨ (False → p2))) ∨ p3) := by
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
theorem thm_5_vars_54946512945498137480235233893 : ((((p3 ∧ (p5 ∨ p3)) ∧ (True → p5)) ∧ (((((p1 ∧ p2) ∨ False) ∨ (False → True)) ∧ ((False ∧ False) → (p1 ∨ p1))) ∧ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52275168315806394990149250104 : (((p1 → ((p1 ∨ (True → (p4 ∨ p4))) → (p4 → (((p1 ∧ p4) ∧ False) ∧ p2)))) → (((True ∨ False) → True) ∧ (p5 ∧ (True ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190275021981797627062852632242 : ((((False ∧ ((p3 → True) → (False ∧ p2))) ∨ p1) ∨ p5) ∨ ((True ∨ ((p1 → (True ∨ ((p5 ∧ p3) → p1))) ∨ False)) ∨ (p4 ∧ (p3 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314435623581275495398380391960 : (p3 ∨ ((p2 ∧ (p5 ∧ (p4 ∨ (p1 → (((((p4 ∨ p3) ∨ True) ∧ (p2 ∨ p1)) ∨ p2) ∧ (True ∧ False)))))) ∨ ((p2 ∧ p2) → (False → p2)))) := by
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
theorem thm_5_vars_60641092743897827003688755457 : ((True ∧ (((p2 → (p5 → p4)) ∧ (((False ∨ ((((p5 → True) ∧ p4) ∧ (p5 ∨ p3)) ∧ True)) → False) ∧ p5)) ∨ (False → (p4 → p4)))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247918753878218459497051424378 : ((p1 ∨ p3) ∨ (((False → ((True → p2) ∧ p1)) → (p5 ∧ False)) → ((p1 ∨ ((p3 ∨ (p3 ∨ p2)) ∧ (p1 ∧ ((p5 ∨ p3) ∧ p4)))) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((True → p2) ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (False → ((True → p2) ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143903767085481728682901960740 : ((((True ∨ (p3 → ((p2 ∧ ((True ∨ False) → p2)) ∨ (p5 ∨ p5)))) → (((p1 → p2) ∨ p3) ∨ False)) ∨ True) ∧ ((False → p2) ∨ (False → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133568667480805490548721380328 : ((((((p4 → ((p4 → (p5 ∧ p4)) ∨ (((True → p1) ∧ (True → False)) → p3))) ∨ False) → (p1 → p2)) ∨ p1) ∧ p2) ∨ ((False ∧ p3) → p4)) := by
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
theorem thm_5_vars_151423317630107752187902870026 : (((p1 ∧ ((((p5 ∧ False) ∨ (p3 ∧ False)) ∨ p4) ∨ ((p2 → (p3 → p5)) → (p2 → p5)))) ∧ (p5 ∨ p3)) → (p1 ∧ (p2 ∨ (p4 ∨ p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- False on the left can always be used.
        apply False.elim h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
  case inr h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h36 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h37 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239593395573259420197094957077 : ((p3 ∨ True) ∧ (((((False → (p3 ∧ p3)) ∨ ((True ∨ p5) ∨ p1)) ∨ (p4 ∨ p3)) ∨ (p1 ∨ p4)) → (p3 ∨ (True ∧ (True → (True ∨ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h5
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h9
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h11
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h13
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h22
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345540143605982862485289655199 : (p3 → ((((p1 ∨ ((p2 → (True ∨ p4)) → p5)) ∨ p2) → ((((True → False) ∨ True) → (p2 ∧ ((p1 ∧ p1) ∨ p3))) ∨ (p4 ∧ False))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57125782395371052702494195824 : ((((p5 ∨ p5) ∧ p5) ∨ (((p2 ∨ (p1 → (((((True → p5) ∨ True) → False) → (False → (p3 ∨ p5))) → True))) ∨ p5) ∧ (p4 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218947279285432246140693948815 : ((p3 ∧ (p2 → (True ∨ p2))) → (((p2 ∧ (False ∧ (((p2 ∧ (p1 → p3)) ∨ ((p4 ∨ False) → (p1 → (p4 → p5)))) → p5))) ∨ True) ∨ p2)) := by
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
theorem thm_5_vars_195497073943918439936192748198 : (((p1 → (p4 ∨ False)) ∨ (True ∨ (p1 ∨ p4))) ∧ (p5 ∨ (((p5 ∧ (True ∧ p5)) ∧ p3) ∨ (True ∨ ((p2 → (p2 ∨ p3)) ∧ (p5 ∨ False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750787212292987494725292340666 : (((True ∧ ((p3 ∨ (((p4 ∨ (p1 → ((p5 → p4) → True))) → p3) ∧ True)) ∨ (False → (p5 ∨ (False ∧ (((p5 ∨ p2) ∨ True) ∧ p4)))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358228713819383160364747551127 : (p5 → (p4 ∨ ((p3 ∧ (((p3 ∧ ((False → ((p2 ∨ (p2 ∧ (p5 ∨ (p1 ∨ p2)))) → p2)) ∨ (p1 ∧ False))) ∧ p1) ∨ True)) ∨ (p1 ∨ p5)))) := by
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
theorem thm_5_vars_731913553202098376379049352167 : ((((p5 → (True ∨ True)) → (((True → ((p1 → p2) ∧ (((((p3 ∧ (p5 ∨ p3)) → p4) → False) ∨ p3) → p5))) ∧ p3) ∧ (p4 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732006782560642741982811499322 : ((((True ∧ False) ∧ (((p2 ∨ True) → (False ∨ ((p3 ∨ (False ∧ (True → (((p2 ∨ (p1 ∧ True)) ∧ True) → p3)))) → (p5 ∨ p1)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207886275801863872907119705688 : ((((p4 ∨ p1) → False) ∧ (True → p1)) → ((((p3 ∨ True) ∨ ((p3 → True) ∨ ((((True → p3) ∧ True) → p4) → p1))) → p1) → (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172205317833742589663993726030 : ((((p2 → (p3 → (p2 ∨ (p3 ∨ p1)))) → (p5 ∨ p3)) → (p4 ∨ (p4 → p5))) ∨ (((p1 ∧ p1) ∧ ((True ∧ (False → p5)) ∨ p4)) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264809139777267348605152023513 : (True ∧ ((p3 ∧ p3) ∨ ((((True → (p4 ∧ p1)) ∧ ((p4 → (False ∧ p1)) ∨ (p4 → (p4 ∧ (p4 → p2))))) ∧ (p3 ∨ True)) ∨ (p5 → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166007417206549480116836321385 : (((False ∨ p3) ∨ ((((p1 → ((p2 ∨ p2) ∧ p3)) → (p1 ∧ True)) ∧ False) ∧ (p5 ∨ p4))) ∨ (((p1 ∨ p5) ∧ p2) → (p4 ∨ (False → p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616960314050384239696029373916 : (((((p1 → (((((p5 → p3) ∧ p2) → p1) ∨ p5) ∧ p1)) → (False ∧ (p1 ∨ (((p3 ∧ (p5 ∨ (p4 → p4))) → p2) ∨ True)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67953203693703207198004847452 : ((p2 → ((((p1 ∧ p2) ∧ False) ∧ p4) ∨ ((False ∧ (False ∧ (p3 ∨ ((p5 ∧ p3) ∨ ((p1 ∨ p5) ∨ (p1 ∨ p3)))))) ∨ (False ∨ p2)))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684845867162451728513415933339 : (((((p1 → p5) → (p2 ∧ (p4 ∨ ((p1 → p4) → (False ∧ ((True → (p3 ∧ p2)) ∨ p3)))))) ∨ (True ∨ (((p1 ∨ p1) → False) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90923543802586441489567624604 : (((True → False) ∧ (p2 → ((((((p2 ∨ (p2 ∨ (((p5 ∧ (False ∧ False)) ∨ (p1 ∧ p4)) → p2))) → p2) → False) ∨ p1) ∨ p1) ∨ p2))) → p3) := by
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
theorem thm_5_vars_693861898478742741583915603580 : (((((p2 ∧ ((((p1 ∧ (True → False)) ∧ False) ∨ (p4 ∨ True)) → p1)) → False) ∨ (p1 → ((True ∨ ((p4 ∧ (False ∧ p5)) → False)) ∨ p5))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197128228928706644638232938170 : (((p4 ∨ (((p1 → p5) ∧ p1) ∧ p3)) ∨ p5) ∨ (((p1 ∧ ((p4 ∨ p5) ∧ True)) ∧ p1) ∨ ((p2 → (p2 ∨ p2)) ∨ (True ∧ (p2 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116369561107035319207468142483 : ((((True ∨ p2) → p3) → ((False ∨ (((((True ∧ (False → p1)) → p5) ∧ p4) ∨ (p3 ∨ (p3 ∨ p3))) ∨ (p3 ∨ True))) ∨ False)) ∨ (p5 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_67767532449803301333986725566 : ((p2 → (((p3 ∧ (((p4 ∧ p4) ∧ p1) ∨ p4)) ∧ (((p4 → p4) ∨ p5) ∨ ((False ∨ (p5 ∨ True)) → ((p5 ∧ p2) ∨ p4)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112621018524374084390694999489 : ((((p2 ∨ ((p2 ∨ (p1 ∨ True)) → (((p5 ∨ ((True ∧ p5) ∨ (p1 → p1))) ∨ p4) → (p4 ∨ False)))) ∨ (p1 → p5)) → p3) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596581918068963781205614673807 : (((((p2 ∨ ((False ∨ (p4 ∧ (False → False))) ∧ p4)) → (((p1 ∧ (p2 → (True ∨ ((True ∧ (True ∨ p3)) ∨ p1)))) → True) → p3)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149411192425279626964807967466 : ((True ∧ ((((p4 → (p3 ∨ True)) ∧ False) ∧ ((True → False) ∨ (p1 → False))) ∧ ((p1 ∨ (p3 ∧ p2)) ∨ p3))) ∨ (True → (p5 ∨ (False → p1)))) := by
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
theorem thm_5_vars_54260773823510554726864816623 : (((((p4 ∧ (p3 → p2)) → p3) → (True → p4)) ∧ ((p5 ∨ False) ∨ (True ∨ ((p5 ∨ (p4 → (((p3 → p4) → p4) ∨ True))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



