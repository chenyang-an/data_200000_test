variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114199255484473246099163367323 : (((((True ∧ ((p1 ∨ True) → p5)) ∨ False) ∧ (p1 → (((p2 ∧ (p5 ∨ (True ∧ p1))) → p4) ∧ p1))) → ((p3 → p1) → p5)) ∨ (p3 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353496252821262789578090747331 : (p4 → (p2 ∨ ((((p1 ∨ ((p4 ∧ True) ∧ p5)) ∧ True) ∨ True) ∧ (((p1 ∧ (p5 ∨ p1)) ∨ p4) ∨ ((True → False) ∧ ((True → p2) ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205504937308330711118469559822 : (((p3 ∧ p4) ∧ ((p2 → p1) → False)) ∨ (((((p1 ∧ False) → (((p5 ∨ True) ∧ p2) ∧ True)) ∧ ((p5 ∧ (p2 ∨ p1)) ∨ False)) ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58500864731580771288274030531 : (((p4 ∨ p4) ∧ (((False ∨ ((p1 → False) ∨ ((True ∧ ((p3 ∨ ((p5 ∨ False) ∨ p1)) ∧ p2)) ∧ False))) → (p1 ∨ (True ∧ p4))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313317950185003462650331384312 : (p3 ∨ ((p2 ∨ (p4 ∧ (((p1 ∨ ((p5 → False) → (p2 ∨ ((((p1 ∨ p1) → p5) ∨ p1) ∨ p3)))) → (True ∧ (p3 ∧ p4))) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695793529856629990363634644735 : (((((p5 → (p1 ∨ p4)) ∨ (p3 → ((True → p1) ∨ (p5 ∧ (p2 ∨ p4))))) → (((((True → p3) → p2) → (p1 ∨ p5)) ∨ False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586517373887640002513661700073 : ((((((False → (False → p5)) → (p4 → ((((False ∧ p1) ∨ p5) → (p1 ∧ (p2 ∨ (True ∨ ((p2 → True) ∧ p1))))) → p5))) ∧ p4) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263159074779549051841238229540 : (True ∧ ((p4 ∧ (True ∧ ((p5 ∨ False) ∧ ((((False ∨ (p5 ∧ ((p3 ∧ p1) ∧ p2))) ∧ (True ∨ (False → False))) ∨ True) ∨ p1)))) ∨ (p3 ∨ True))) := by
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
theorem thm_5_vars_266118321591718008822929079053 : (True ∧ (p3 → ((((((p1 ∨ (True ∧ p4)) ∨ True) → (p3 → (p5 → ((p5 → (p2 ∧ True)) ∨ p4)))) → (p4 ∨ (p4 ∧ False))) ∧ p2) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47853179547034613784360142892 : ((((p1 → (((p5 ∧ p4) ∨ ((p4 ∨ p4) ∨ p4)) ∧ ((p1 → ((((False → True) → p5) → p3) → True)) ∧ p1))) → p1) → (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356838652715623062899059322926 : (p5 → (((False ∨ (p4 → False)) ∧ p3) ∨ (((((((p4 ∧ False) → (p5 → (p3 → (p2 → p1)))) ∨ (p5 ∨ p4)) ∧ p4) → p2) ∨ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733339110171481775753343068146 : ((((p3 ∧ p5) ∧ (True → ((((p1 → p1) → p2) ∧ (p1 ∧ p4)) ∨ ((False ∨ False) ∨ ((p1 ∨ p3) ∨ (((p4 → p4) → p3) → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330743572281746143811654824441 : (True → (p1 → ((p4 ∨ ((p2 ∨ True) ∧ ((p1 ∨ (p1 ∨ (p5 → p2))) → p4))) ∨ ((p4 ∨ ((False ∧ p3) → (p1 ∨ (p3 ∧ p3)))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47372903097274546776201002023 : ((((p5 → p4) ∨ (((p2 ∧ (p4 → (True ∨ p1))) ∨ (p3 → (p3 ∧ p1))) ∧ ((True ∧ (p5 ∧ False)) ∧ (p3 → p5)))) ∨ (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114569494505150584191428509293 : ((((p5 → (p5 → ((((p5 → p4) ∨ p2) ∨ p1) ∧ (p1 ∧ p1)))) ∨ (p1 → p4)) ∧ (False ∧ (p4 → ((p2 → p2) ∨ p1)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172461290161477091461131336148 : (((p1 ∨ ((p2 ∨ p5) ∧ p1)) ∨ (((p1 ∧ p4) ∧ True) ∧ ((p1 ∨ True) ∨ p3))) ∨ (True ∨ (False → ((p3 ∧ p1) ∧ ((p3 ∧ True) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148041708366000335404679181959 : ((((p5 → True) → ((p5 → (((p3 → p4) → (p5 → p3)) ∨ (True ∧ (p1 ∧ p1)))) ∨ p5)) ∨ (True ∨ p4)) ∨ (False ∨ (p3 ∨ (p5 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47176375355988582102879239968 : ((((((False → False) ∧ (p4 ∧ ((p2 ∨ False) → ((p3 ∧ p4) → p1)))) ∧ p1) → (p5 ∧ ((True ∧ (p5 ∨ p1)) ∨ p3))) ∨ (p2 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350256267223168681251501146886 : (p4 → ((p1 ∧ (((False ∧ p3) ∨ p2) ∧ (True → (p4 → (((False ∧ (p4 ∧ (((p1 ∨ (p4 ∨ False)) ∧ p3) ∨ p4))) ∧ p3) ∧ True))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8768872218995194096298526802 : ((((((False ∧ False) ∨ ((((p3 ∧ p4) → (p1 → ((False ∨ False) ∨ p5))) ∨ (p1 → True)) ∧ p3)) ∨ p3) ∨ ((p4 ∨ p4) → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_347518065119969252401033144790 : (p3 → ((((True ∨ True) → False) ∧ (False ∨ p4)) → (p5 ∨ (((((p3 → (True → (False → p3))) ∨ (p1 → (p2 ∨ p2))) ∨ p3) → p1) ∨ p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761347216252040715599741374145 : (((p3 ∧ ((((((p5 ∧ p5) ∧ (p2 ∨ p3)) ∧ ((p3 ∧ (p1 ∧ p1)) ∧ p1)) ∨ p2) ∧ (((p5 ∧ p4) ∧ (p4 → p5)) ∧ True)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311853470457743346543340742479 : (p2 ∨ (p1 ∨ (p1 → ((p2 → ((False ∧ (p4 ∧ ((p4 ∨ p4) ∧ p1))) ∨ ((p3 ∧ p1) ∧ p3))) ∨ ((True ∨ False) ∧ ((p4 ∨ p3) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61037277368237320691053837779 : ((False ∧ (((p3 → ((((False → ((((p4 ∨ p5) → p5) → (True ∧ p4)) → (p4 ∨ p4))) ∧ p2) → p5) ∨ True)) → p2) ∨ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328120996710066845403947037163 : (True → ((((False ∨ (p1 ∨ (False → True))) → (p1 ∨ (True ∨ (True → False)))) → ((p3 ∨ p5) → ((p2 ∨ False) → False))) ∨ ((p2 ∧ p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221523829461410345711445365621 : (((p2 → p2) ∨ True) ∧ ((p1 → ((p3 → (False → (p4 ∧ ((p2 ∧ ((True ∧ p5) → p1)) ∧ p5)))) → (((p4 → False) ∧ p4) ∨ True))) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191434641176108331694078811937 : (((p4 ∨ False) → ((False ∨ False) ∨ (p2 ∧ (p2 → False)))) ∨ ((((False ∨ ((True → p1) ∧ p5)) ∧ (p1 ∧ False)) → p3) ∧ (p5 ∨ (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184885631763349800321687065767 : (((p3 ∨ (p4 ∧ p2)) ∧ (((p1 ∧ p2) ∧ True) ∨ (p3 ∧ True))) ∨ ((True ∨ (p2 ∨ p2)) ∧ (False ∨ (p2 → (p2 ∧ (p4 → (p2 ∧ True))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169989834899380074912991523355 : (((((p1 ∧ p5) → True) ∨ (p1 ∨ ((True ∧ p3) → p3))) ∧ (False → (p2 → p4))) ∧ ((p4 → ((p2 ∨ (False ∨ (p2 ∧ p1))) ∧ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186332890012813753856961572312 : (((((p4 → p4) ∨ (p1 ∧ False)) ∨ ((p3 → True) ∧ p3)) → p1) → (((p2 ∨ (False ∧ ((p4 → (True ∧ p2)) ∧ (p1 ∧ True)))) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171476643580184250057577648705 : (((p4 ∨ ((False ∨ ((p1 ∧ (p1 → True)) ∧ False)) ∨ ((p4 ∧ False) ∨ True))) ∧ p3) ∨ (p1 → (p4 → (p2 → ((p2 → p2) ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54803382146633096557612872513 : (((p1 ∨ ((p2 ∨ ((True ∧ p1) ∧ False)) → p4)) → ((p1 → (((p2 ∧ ((True → p5) → False)) ∨ p1) → False)) ∨ ((p3 → p3) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_735681146389990727424102014088 : ((((p5 ∨ p2) ∧ ((p5 ∨ ((p3 → ((False ∧ ((p1 ∧ True) ∨ (p3 → p5))) → (p1 ∧ p3))) ∧ p2)) ∧ (p2 → ((p5 ∧ p1) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135055819931220596118367214968 : ((((((p3 → (((True → p2) ∨ (p2 ∧ p2)) ∧ ((p4 ∨ p2) ∨ (p3 ∨ p4)))) ∨ False) ∨ p2) → False) ∨ (True → True)) ∨ (True ∨ (p1 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190493736143393943805215261279 : (((((p2 ∨ (True ∧ (p1 ∨ p2))) → True) ∨ False) → p2) ∨ (True ∨ (p5 → (((p5 ∨ p5) ∧ ((p5 → p5) ∨ False)) → ((p1 ∧ p2) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70253449486994114950613547820 : ((((((True ∨ p3) → (((True → (p3 → ((((p2 → True) ∧ p4) ∧ p2) ∨ (True ∨ p2)))) ∨ False) ∨ p2)) → p3) ∧ (p3 ∨ True)) ∧ p5) → p3) := by
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
    exact h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : ((True ∨ p3) → (((True → (p3 → ((((p2 → True) ∧ p4) ∧ p2) ∨ (True ∨ p2)))) ∨ False) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h8
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135051155327188302175327910830 : ((((p1 ∧ ((True → ((True ∧ ((((True → p4) ∨ p2) ∨ False) ∧ True)) → (p3 ∨ p1))) ∨ p4)) ∨ True) ∨ (p2 ∨ p5)) ∨ (True ∧ (p1 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67960970620606615762323641717 : ((p2 → ((True ∨ (p3 ∨ (p5 ∨ p4))) → (((((p5 ∨ (p3 ∨ (p4 ∧ False))) → p1) ∧ (True ∧ (p3 ∧ (p3 → p4)))) ∨ p2) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323198521334335758556560074703 : (p5 ∨ ((((True ∧ (((p3 ∧ (((p3 ∨ (p2 → True)) ∧ False) ∨ p5)) → p4) ∨ (False ∧ (p3 ∧ p3)))) → False) ∧ (True ∧ p4)) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337946950426772782320351624474 : (p1 → (((p1 ∧ ((p3 ∧ (p5 ∧ (p4 ∨ p2))) ∧ p2)) ∧ (p4 → False)) ∨ ((p4 → (True ∨ ((p1 ∨ (p4 ∨ True)) ∧ p1))) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_785505872907865185843613940415 : (((p4 ∨ (((p4 → p2) → (False ∨ ((p5 ∨ p3) ∨ ((p2 ∨ (p5 ∨ (p5 ∨ (p1 ∧ (p2 → ((True → p5) ∧ p3)))))) ∧ p1)))) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_691400166832394963942523112931 : (((((False ∨ p3) ∧ (p3 → (p3 ∧ (p3 → ((((p2 → True) ∧ p3) ∨ p1) → p5))))) → ((((p4 ∧ True) ∧ (False → True)) ∨ p1) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259874628988675655747471279659 : ((p1 → p4) → ((p5 → (((False ∨ (p4 ∨ False)) → (((False ∨ (False → p5)) ∨ (False ∨ p4)) → p2)) ∨ True)) ∧ (False → (p5 → (False ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247427050818310186881658990548 : ((False ∨ p2) ∨ (((p3 ∧ (((p1 ∨ (p4 → p3)) ∨ (p3 → p5)) ∧ p1)) ∨ (False ∧ (p4 → p2))) ∨ (p5 ∨ ((p5 ∧ False) → (p4 ∨ p4))))) := by
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
theorem thm_5_vars_156762772919440906484691176670 : ((((True ∧ p4) ∨ (((p5 ∨ ((p3 → (p1 ∧ (p3 → (False ∨ False)))) → False)) → p2) ∧ p2)) ∧ True) ∨ ((p5 ∨ (p3 → p5)) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340887484031036117431972522875 : (p2 → (((((p3 → p4) ∧ p1) ∧ (((p5 ∧ p1) ∨ (p5 ∨ (False ∧ True))) ∧ p4)) ∨ ((((p1 → (p3 ∨ False)) ∨ p2) ∨ p2) → p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215367233090172307781167039404 : ((p2 ∧ ((p5 ∨ p3) ∨ p2)) ∨ ((p4 → p3) ∨ (((((p2 → (False ∨ False)) ∧ (p4 ∧ p5)) → (p2 → (p3 ∨ (True → False)))) ∨ p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136140734116614576700695265669 : ((((p3 ∨ (((True → p4) ∨ False) ∨ p5)) → p3) → (p2 ∧ (((p1 ∨ (p5 → p2)) ∨ ((p3 → True) → p1)) ∨ p1))) ∨ ((p3 → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126802057931294897163624148572 : ((p5 ∧ (((p4 ∨ (p5 ∨ ((p4 ∧ True) ∧ ((p2 ∧ (p4 → p3)) ∨ ((p3 ∨ (p2 ∧ p4)) → (p4 ∨ p5)))))) ∧ False) → p1)) → (p3 ∨ True)) := by
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
theorem thm_5_vars_633986105715737485091320275 : ((((p5 ∨ p1) ∧ (p5 → ((((p5 ∨ (False ∧ (p5 → p4))) → p2) ∧ (True ∧ p5)) ∧ (p2 → (True ∧ p1))))) → (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225181461209365086444067366543 : (((p4 ∧ p1) ∧ p2) ∨ ((False ∧ (((p4 → (p2 → (True ∨ p2))) ∨ ((False ∨ (p1 ∧ True)) ∧ p1)) ∧ False)) ∨ (False ∨ ((True ∨ p5) ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314402096035849872017259594754 : (p3 ∨ ((((p4 ∧ (p1 → (p5 → (True → False)))) ∧ ((p1 ∨ p2) → ((p5 → (p4 ∨ p5)) → p4))) ∧ False) ∨ (p4 → ((p3 → p4) ∨ p3)))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149988215811054410108256210712 : ((p4 ∨ (p3 ∧ (((p5 ∧ p1) → (True ∧ (((p2 ∧ ((p4 ∨ p4) ∨ True)) ∨ False) ∧ p1))) ∨ (p4 ∧ p3)))) ∨ (p4 → ((True → p4) ∧ p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48194110663914113338368995556 : ((((False → p3) ∨ (((True ∨ ((p2 ∨ p2) → ((p4 ∧ (p4 → ((p1 → p3) → (p5 ∨ p3)))) ∨ True))) ∨ p4) ∨ p5)) → (p4 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149809003692749453731895655485 : ((False ∨ (p1 → ((p5 ∧ (((p2 → False) ∨ ((p5 → (p3 ∨ p2)) ∧ p3)) ∨ p5)) ∨ (True ∧ (False → p4))))) ∨ ((p3 → True) ∧ (p3 → p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117464782711137394058788296164 : ((p1 ∧ (True ∧ ((p2 ∨ ((((((p5 → False) → p5) ∧ p4) ∧ ((p1 ∧ p1) ∨ p5)) ∧ p1) → ((p5 ∨ p5) ∨ p3))) ∨ p4))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713911260079602427411148808879 : (((((p3 ∧ ((True → p2) ∨ p4)) ∨ p2) → ((((p5 ∨ p3) → p4) ∨ True) ∨ (True ∨ ((True → (True ∨ p3)) → ((True ∨ p5) ∨ p5))))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113024262915235260332441615120 : (((True ∨ ((True ∨ (((True → (p3 → p3)) ∨ (p5 → (((p1 ∧ p5) → True) → ((p4 ∧ p4) ∧ False)))) ∨ p2)) → True)) → False) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227842026906867938948110352642 : ((p2 ∧ (p5 ∧ p3)) ∨ (((((p2 → p2) → ((((p1 ∨ p3) ∨ False) ∨ True) ∨ False)) ∧ p3) → p5) → ((p3 → (p4 ∨ (p3 ∧ p5))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 → p2) → ((((p1 ∨ p3) ∨ False) ∨ True) ∨ False)) ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57546062382096766125369731709 : ((((p1 ∧ p1) ∧ p3) → (p5 ∨ (((((p3 ∨ ((True ∨ (((p1 ∨ p4) ∨ p4) ∧ p4)) ∨ p1)) ∧ (p2 ∧ p4)) ∨ p3) → p4) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299195232434627232736557930769 : (False ∨ (((p5 ∨ (((p1 ∧ p1) ∨ ((p4 ∨ p3) ∧ ((p2 ∨ (False ∧ p4)) ∧ (p1 ∨ p2)))) → ((p2 → (False ∧ p4)) → True))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138374845179373203234938955331 : ((p4 → (((True ∧ (p2 ∨ p4)) ∧ p2) ∨ (((False ∨ p5) ∨ ((True → p2) ∨ (((p5 ∨ p1) ∨ p3) → p4))) ∨ p1))) ∨ (p3 ∨ (p1 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208976853036793761455678111921 : ((True ∨ (True ∨ (True → (p1 → False)))) → ((((p4 ∧ ((((p2 ∨ p3) → (p5 → p2)) ∧ p5) ∨ p3)) ∨ ((False ∧ p5) ∧ p2)) ∨ p5) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178506360922535027758170115629 : (((p3 → ((p4 ∨ ((p4 ∨ p5) ∧ p3)) ∨ p2)) ∨ ((True ∧ p3) ∨ p2)) ∨ ((((True ∨ p3) → False) ∨ p2) ∨ ((p5 ∧ (p1 ∨ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260251861369816229833996875225 : ((p2 → p3) → (((p4 ∨ p5) → p2) ∨ (True → ((((True ∨ False) ∧ False) → True) ∧ (((p4 ∨ p3) ∨ (p3 ∧ ((p4 ∨ p1) ∨ p2))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713440268798153486339946079499 : ((((p2 → (p1 ∧ (p3 ∧ (False ∧ p4)))) ∨ (p1 → (p2 ∧ ((True ∨ (((p4 → True) → True) → (p1 → (False ∧ p3)))) ∧ (p4 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49819088101965039900023127587 : (((p2 → (((((p5 ∨ p5) → p3) ∧ (p4 → (True → False))) → ((False ∧ False) ∧ p5)) ∧ (p3 → (p2 → p1)))) → ((p4 ∨ p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160530978613694621224670537807 : (((((p3 → p3) ∨ ((False ∧ (False → p5)) ∧ p2)) → (p2 ∨ p3)) ∨ ((False ∨ p5) ∧ (True → True))) → ((p3 ∨ (p4 → p1)) ∨ (False → p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337773675690078032160178397221 : (p1 → (((p3 ∨ p3) ∧ ((False ∨ (True ∧ (p1 → (p5 ∨ p5)))) ∧ ((True ∧ p4) ∧ p3))) ∨ ((((p3 → p4) → p1) → (p1 ∧ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156765478167065580239343658546 : ((((False ∨ p1) ∨ ((p2 → (p5 → p3)) ∨ (p5 → ((p3 ∧ p5) → (p2 → (p3 → p4)))))) ∧ p1) ∨ (p3 ∨ (((p3 → True) ∧ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125130976142942232942608693548 : ((((False → p4) ∧ p1) ∨ (p5 ∨ (p5 → ((p4 ∧ (False ∨ ((p3 ∧ p3) ∧ ((((p2 ∧ p4) → p3) → p5) ∧ p2)))) → p1)))) → (p4 → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336209784203134520708735063910 : (p1 → ((((False → (p2 ∧ (p2 ∨ ((((p5 ∨ True) ∨ (False ∨ p4)) → (p1 ∧ p4)) ∧ True)))) ∧ ((p3 → True) ∧ p1)) → (p2 → p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41484686936816794175254654704 : ((((False ∨ ((False ∨ (p2 → (p2 ∨ p4))) ∧ (p4 ∨ (p2 ∨ False)))) ∨ ((p4 ∨ (False ∨ ((True ∧ False) → False))) ∧ (True ∨ p4))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171648729291384888376115072539 : ((((p4 → True) → (((p5 ∧ p5) → (False → (p4 ∧ (p3 ∨ p4)))) → p4)) ∨ p4) ∨ (((True ∧ ((p2 ∧ p2) → True)) ∨ p2) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709472288441706009020439349578 : ((((p3 ∧ (False ∨ (((p2 ∨ False) → p3) ∨ p5))) → (p2 ∨ (((((False ∧ p2) ∧ p1) ∧ True) ∨ (((p5 ∧ p3) → False) → p5)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780846850237473587665330310763 : (((p2 ∨ ((((True → False) → False) → True) → (((False ∧ p2) ∨ (((p3 → p1) ∧ (p5 ∨ p1)) ∧ ((True → p1) → p4))) ∨ (p4 → p4)))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346182517272615122857363002485 : (p3 → (((p4 ∨ ((((False ∨ True) ∧ (False ∧ (p4 → p2))) ∧ ((False → (p2 ∨ (p1 → (False → p2)))) → p2)) ∧ p3)) ∨ True) ∧ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181655428678916170973633136123 : ((p3 → (p5 ∧ ((p2 → p3) ∧ (p3 → (p5 ∧ ((p2 ∨ False) ∧ False)))))) → ((((True ∧ False) ∨ (p1 ∧ False)) ∨ p3) → ((p2 ∧ p1) ∨ p2))) := by
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148728370242089450080082478256 : (((p4 → ((False ∨ (True → (True ∧ p1))) ∨ p2)) → (((p4 → ((p3 ∧ (p1 ∧ p3)) ∧ True)) → p2) → p3)) ∨ (((False ∧ p1) ∨ False) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179814406457869689918710358771 : (((True ∧ ((False → (p3 ∧ (p1 ∨ ((False ∧ p1) → p1)))) ∧ p5)) ∧ True) → (p3 ∨ (((p3 ∨ p5) ∨ p4) ∨ ((p1 → (p1 → p5)) → p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312399770832962041111598844687 : (p2 ∨ (p3 → (p1 → ((((((True ∧ (p1 → (p4 ∧ (False ∨ (p4 ∨ ((p3 ∧ p4) → p2)))))) ∨ True) ∧ False) ∨ False) ∨ (p1 ∨ p4)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172117731098544663643901949490 : (((((p5 ∨ (p3 ∧ p1)) → (p1 → (p4 ∨ p2))) ∨ p4) ∧ (False ∧ (p4 ∨ p3))) ∨ (((p5 ∧ p1) → ((p5 ∧ (p1 ∨ p3)) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652748421354821389784564193788 : ((((p2 ∨ (((p5 ∧ (((p1 → p5) ∨ (True → (True ∧ p1))) ∧ p3)) ∧ p2) ∨ (True ∧ (((p1 → False) → p2) ∨ False)))) ∧ (p2 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177626025588274959550229880926 : ((((((p1 ∨ p4) → (((p3 → p4) → False) ∧ p2)) ∧ p5) ∧ True) ∧ p3) ∨ ((p5 ∧ (False ∨ (p3 → p1))) → ((False ∧ (p5 ∧ p2)) → False))) := by
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
theorem thm_5_vars_326301169917700921135745731844 : (p5 ∨ (p4 → (((((p5 → ((p4 ∧ p4) ∨ True)) → p5) ∨ (True → p3)) → (False ∧ p4)) ∨ (False → (((p2 ∧ (p2 → p4)) ∧ p4) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937258585235113037446066144446 : ((((((p5 ∧ p2) ∨ p2) → (p5 ∨ p3)) ∧ ((True ∧ ((p5 → ((p5 ∧ True) ∧ p1)) ∧ p1)) ∧ ((False → (p1 → (p5 → p4))) ∨ p1))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258798077261465187666730290196 : ((True → False) → ((p2 ∨ False) ∨ (((((p4 ∧ p2) ∨ p1) ∧ p4) ∧ ((p1 → (p1 ∧ True)) ∧ ((p3 → (p5 ∧ (False → p2))) ∨ True))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57294584132731344722611425130 : ((((p2 → p5) → p2) ∨ (True ∧ (p2 → ((p2 ∨ (((p1 → True) ∨ (p5 ∨ p2)) → ((p5 ∧ (p4 → True)) → p5))) ∧ (False ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227657656696715164416332796032 : ((False ∧ (False → p4)) ∨ (p1 → (((p5 ∧ p1) ∨ p5) → ((p5 → ((p2 ∧ (p3 → True)) ∨ (p2 ∨ ((p2 → p1) ∨ (p4 → p3))))) ∧ p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136063133693147280753151559184 : ((((((p3 ∧ p5) ∨ False) ∨ True) ∨ (False → p4)) ∧ ((p3 ∧ ((p4 ∧ ((p3 ∧ p4) ∨ (p5 ∧ False))) → p4)) ∧ p3)) ∨ (p3 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51431438805244666942730230267 : (((((p3 → ((p2 ∧ p3) ∧ ((p1 → ((False ∧ False) ∨ False)) ∨ p4))) → False) ∨ (p4 → p5)) → (p5 ∨ (p1 → ((False → False) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88086253074651853899316208451 : (((((True ∧ False) ∨ p2) → True) ∧ ((p3 ∨ ((p1 → p4) ∧ p5)) ∧ (((True ∨ p5) ∨ (p1 → (False ∧ False))) → ((p5 → True) ∧ p2)))) → p2) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∨ p5) ∨ (p1 → (False ∧ False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h13 : ((True ∨ p5) ∨ (p1 → (False ∧ False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340789560121621906205687410014 : (p2 → ((((((p3 ∨ p5) → p1) → True) ∧ ((p4 ∨ False) ∨ ((p3 ∧ False) → (((p2 ∧ (p5 ∨ p4)) ∨ (p3 → p5)) ∨ True)))) → p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119499460036038910454169794747 : ((p4 → (p2 → (((True → (False → (p2 → (((p5 ∧ p3) ∧ p3) → False)))) ∨ p5) → (p5 ∧ (((True ∧ p5) ∧ p1) ∨ p4))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304719476196280776237923940451 : (p1 ∨ ((((p3 ∨ (p4 ∨ p2)) ∧ ((p3 ∧ ((True → (True ∧ (False ∧ (p1 → False)))) ∨ p3)) → p2)) → (p4 ∨ (p2 → p1))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_853173675579370651644214267 : ((p2 ∨ ((p3 ∧ ((True → p2) ∨ p2)) ∨ ((p2 ∨ ((False ∧ (p1 ∨ (p4 ∨ p1))) ∨ ((p5 ∨ (p4 → True)) → p2))) ∨ True))) ∨ p1) := by
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
theorem thm_5_vars_113613293759267535387204934222 : (((p4 ∨ (p5 ∨ ((p5 ∧ (((p3 ∧ p3) ∧ ((True → (True ∨ p2)) ∨ (p3 → p3))) ∧ p5)) ∧ (False ∨ p3)))) ∨ (True → p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305166137890011312523153241620 : (p1 ∨ (((p4 ∧ (((p3 → p4) ∧ (p1 ∨ p4)) ∧ (p3 → ((p1 ∨ (p3 → (p4 ∧ p4))) ∨ p1)))) → p5) ∨ ((p4 ∧ p5) → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38323965923272122590510798036 : ((((p3 ∨ ((p2 ∧ (False → (p5 ∨ ((((p2 ∧ False) → p4) → p5) ∧ (p5 ∨ p4))))) ∧ p5)) → ((True → p1) ∨ (False ∨ p1))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184406836568062740642072493032 : (((((p2 ∧ ((False → False) ∧ p5)) ∨ p4) ∨ p4) ∧ (True ∨ p2)) ∨ ((p2 ∨ (False → (True ∧ (((False ∨ p1) → (p5 ∨ p5)) → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



