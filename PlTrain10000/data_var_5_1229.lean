variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8246570660784143423091852615 : ((((((((p3 → ((p5 ∨ p3) ∨ p3)) ∧ ((True ∧ p1) ∨ (p3 ∧ (p1 ∨ False)))) → p5) ∧ ((p4 ∧ p1) ∨ p5)) ∨ p5) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61073157254809650458679852702 : ((False ∧ ((True ∧ (((((p3 ∨ p1) ∧ (p1 ∨ p5)) → ((p3 ∧ (p4 ∨ p1)) ∧ p5)) ∨ (p3 ∧ p5)) ∧ True)) → (p5 ∧ (p4 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324490906660141697619160190299 : (p5 ∨ (((p1 → (p2 ∨ p3)) → p1) ∨ (((((p4 ∧ False) ∨ (p5 ∧ ((p5 → False) ∧ p2))) ∨ (((True → True) ∧ True) ∧ p3)) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174051706866455255416314194678 : (((p1 → ((p4 → p3) → ((p2 ∨ p3) ∧ ((p3 → (p3 ∧ p4)) ∨ True)))) → p4) → (p3 ∨ (p3 → (((True ∧ False) ∧ p4) → (p2 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165627544342172837184486594915 : ((((p2 → (False → (p3 → p4))) → p3) ∧ (False → ((((p4 → p4) ∧ p3) ∨ p2) ∨ False))) ∨ (False ∨ (((p3 ∧ True) ∧ p1) → (True ∨ False)))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161229733013066230157888692113 : (((False ∧ False) → (False ∨ ((p5 ∧ (((p1 ∧ p4) → p2) ∧ ((p1 ∧ (p1 ∧ False)) ∧ p4))) → p4))) → (p2 ∨ (((p1 ∧ True) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42503870413278157877315467828 : (((False ∨ (((p4 ∨ p3) ∨ (False → (False → (True → ((p1 ∨ False) → (True ∧ p1)))))) → (p3 → (p1 ∧ ((p2 ∧ p4) → p5))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177685389844032468917056518290 : ((((True → (((p3 ∧ p2) → (p5 → (False → p3))) ∧ p1)) → p2) ∧ p1) ∨ ((p2 ∧ (p4 ∧ p1)) → ((p3 ∨ (False ∧ p2)) ∨ (p1 ∧ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669789731612551222671128124071 : ((((((p5 ∧ (((p3 ∧ True) → (p1 ∨ p3)) ∨ (p3 → p3))) ∧ (p1 → True)) → (p5 → ((True → p4) ∧ True))) ∨ ((True ∨ p5) → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_316426306986276251850449017010 : (p3 ∨ (p1 ∨ (((((((p1 → (p3 ∨ True)) → p3) ∨ False) → (p4 → (p5 ∨ (p1 ∨ (p3 ∨ False))))) ∧ (False → (False → p3))) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40748315779810636847715107704 : (((((p2 ∨ (p2 → False)) → ((False → ((p2 ∨ (True ∧ ((p3 ∧ False) ∧ (p1 ∨ p1)))) ∨ ((p3 ∧ p3) ∨ p3))) → p3)) → p2) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781087991626019479593808674883 : (((p2 ∨ ((p2 ∧ p1) ∨ (((p4 → (p5 → ((p1 → False) → (((p2 ∧ (p4 ∨ p4)) ∨ ((False ∨ p2) → p1)) ∨ False)))) → p3) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51642143812402872098172269810 : (((((p2 ∨ (p4 ∧ (p3 ∧ p4))) → (((False ∨ p2) → (p1 ∨ p5)) ∧ p4)) ∨ p1) ∧ ((False ∨ (False ∨ ((p1 → p1) → p4))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617214766609253140881422404052 : ((((((p5 ∧ p5) ∧ (((p3 → True) → p3) → p4)) ∨ (((p3 → (False → ((p5 ∧ (p1 ∧ p3)) → (False ∨ True)))) ∨ p5) → False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149259789983838078684618428391 : (((p4 ∨ p1) ∨ (p5 ∨ (((p1 ∨ ((p2 ∨ p4) ∨ (True ∧ p5))) ∧ (p4 → p5)) ∨ (p1 ∨ (p2 → True))))) ∨ ((p1 → True) ∧ (p3 ∧ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313102390171315119737503133405 : (p3 ∨ (((((p3 ∧ p1) ∨ (((((True ∨ p2) ∨ (p2 ∧ (p2 ∨ False))) → (True ∧ p2)) ∧ p4) → p4)) ∨ p2) ∧ ((p1 ∨ p5) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158597063502222789278097812299 : ((False ∧ (((True ∧ p4) ∨ (True ∧ (p2 ∧ (p1 ∧ ((True → p2) ∧ (p2 → (p4 ∨ p2))))))) ∨ p5)) ∨ (True ∨ ((p3 ∧ (p5 → p1)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225319028022447295051209391820 : (((False ∨ p4) ∧ p5) ∨ ((p4 ∧ p5) ∨ (((False ∧ (((p2 → (p4 → p2)) ∧ False) ∨ ((p1 → False) ∧ (False → (p3 ∧ True))))) ∨ False) → p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149160618127349782113169593237 : (((p3 ∨ True) ∧ (p4 ∨ (((p3 ∨ (((p4 → p4) → p3) ∨ p1)) ∨ (False → (True ∧ p3))) ∨ (False → p4)))) ∨ (p2 ∧ ((p3 ∧ False) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37750266093566674630151909705 : (((((((True ∧ (False ∧ p5)) ∨ False) → True) → (p5 ∧ (p3 ∨ (((True ∨ p2) ∧ (True ∨ True)) ∨ ((p5 ∨ p2) ∨ p4))))) → False) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717184064316394559429068879915 : ((((p1 ∨ (p4 → (False ∨ False))) ∧ ((p2 → ((True → (p4 ∧ (p5 ∧ p3))) ∧ p1)) ∧ ((p4 ∧ ((True → p5) ∨ (False ∨ True))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111837261809056682124802233510 : ((((((p4 → ((False ∨ (p1 ∧ p1)) ∧ (p1 ∨ p1))) ∨ p2) ∨ ((p1 → (p3 ∧ p2)) ∧ p3)) ∨ ((p5 ∨ True) → p1)) ∨ False) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313986818555540371058942412540 : (p3 ∨ ((((p2 → (p2 ∧ p2)) → p3) ∨ (((True ∨ p1) → ((p3 ∧ (((p5 ∧ p2) → p4) ∨ p4)) ∨ p3)) ∨ (p4 → p5))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612465436815373299323658319757 : (((((((False ∧ (p4 ∨ ((p4 ∧ (p1 ∧ (p3 → p2))) ∨ p3))) ∨ ((p5 → p2) ∨ ((False ∨ p1) → p3))) ∧ p3) ∨ (p2 ∨ p1)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_317725147920692760230670620345 : (p4 ∨ (((((p4 ∧ ((((False ∧ True) ∧ ((p1 ∧ p2) ∨ (p4 ∧ (True ∨ p3)))) ∨ True) → p5)) ∨ p1) ∨ p2) ∧ (True ∧ (p1 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136418823485059139089671680873 : (((((p5 ∧ True) ∨ p4) ∨ p3) → (((p3 → (p3 ∧ p5)) → ((p5 → p5) → ((p3 ∨ False) → p5))) ∨ (p2 → True))) ∨ (False ∨ (p1 ∨ False))) := by
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
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76498527180572052351163282888 : ((((p3 ∨ (p1 ∧ ((p4 → (p1 ∧ ((p2 ∨ p5) ∨ (p3 ∧ (((p4 ∨ p2) ∨ True) ∨ p1))))) → p2))) ∨ ((p2 → p2) ∨ p1)) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ (p1 ∧ ((p4 → (p1 ∧ ((p2 ∨ p5) ∨ (p3 ∧ (((p4 ∨ p2) ∨ True) ∨ p1))))) → p2))) ∨ ((p2 → p2) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117671293996623245601703276989 : ((p3 ∧ ((p5 ∨ ((((p2 ∧ (p3 ∧ p3)) ∧ (False → p2)) → False) ∧ False)) ∧ ((p2 → (p2 → ((p4 ∧ True) → False))) ∧ False))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230873455089347870285044654452 : (((p1 ∧ p5) ∨ p4) → ((p1 ∧ (((p2 ∧ ((p1 ∨ ((False → True) ∧ p1)) ∨ ((p3 ∨ p1) ∨ ((p4 → p1) → p2)))) ∨ p4) ∧ p2)) ∨ True)) := by
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
theorem thm_5_vars_115765799925398113445578715714 : (((p4 ∨ (p2 → ((p5 ∧ p5) → p1))) → ((((p5 ∧ (((p4 → p4) ∧ (p5 ∧ False)) → (True ∧ p1))) → p3) → p5) ∨ True)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301849908559375277073837939795 : (False ∨ ((True → p3) ∨ ((((p2 ∧ p3) ∨ (p3 → (p4 ∨ True))) ∨ p4) ∧ (((((True → (False ∨ p3)) ∧ (False ∧ p3)) ∨ True) ∨ p5) ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_148705177235325430221239496339 : ((((p4 → (False ∧ ((True ∨ p5) → p1))) ∨ p1) → (((p4 → ((p5 ∧ p1) → p1)) ∧ p4) ∨ (p1 → False))) ∨ (((p5 ∨ p1) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59023760933309550435765977934 : (((p4 ∧ True) ∨ (((False ∨ (((p3 → (((p4 ∨ p1) ∧ (p3 ∨ p5)) ∨ (False ∨ (True → False)))) → True) → p2)) ∧ (p3 ∨ p1)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644499133437507283399513669298 : ((((p1 ∨ ((((p2 ∧ p1) ∨ (p3 ∧ (((p1 ∧ (p1 → p5)) → (((p1 → p5) ∧ p1) ∧ p2)) ∧ (p4 → p5)))) ∨ False) ∨ p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114425560587202276621011625997 : (((p1 ∧ ((((p5 → p1) → p2) ∨ p2) → ((p5 ∧ (p3 ∧ ((p4 ∧ False) → p2))) ∧ False))) ∨ (p5 → ((p1 ∨ p1) ∨ p5))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1503790942462751850096836290 : (((p2 ∨ ((((p4 → p2) ∨ p2) ∨ ((True ∨ (False ∨ (p5 → p2))) ∨ False)) ∧ p4)) ∧ (p1 → ((p5 ∨ True) → p2))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55411050528468423726588554460 : (((((True ∨ (p4 → p5)) → p1) ∨ p4) → ((((p5 ∨ (p2 → (p5 ∧ (p3 ∧ (True → (p1 → True)))))) ∨ (p4 ∨ True)) ∧ False) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615469078432482912830068345049 : ((((((((p1 ∧ (True → p2)) ∧ (p4 ∧ (False → p2))) ∧ (p4 → (p4 ∨ p5))) ∨ p3) → ((p5 ∨ (p3 ∨ p2)) ∨ (p3 ∧ p3))) ∨ p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124496102369437100307496462009 : (((((True ∧ (False → True)) ∨ p3) → p2) ∧ (False ∨ ((((p5 ∧ p4) ∨ p4) ∨ ((p3 ∨ p3) ∨ (False ∨ (p4 ∧ p5)))) → p3))) → (True ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((True ∧ (False → True)) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168412889683316244774875659045 : (((p2 ∧ p2) → (False → (p2 ∨ (((True → (p1 ∧ (p5 ∧ p2))) ∧ (p2 ∨ p2)) ∧ True)))) → (True ∧ (((p2 ∧ p1) ∨ p4) ∨ (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149701475396461989023560449003 : ((p5 ∧ ((p2 ∧ p1) ∧ ((p1 ∨ (((False ∨ p5) ∧ p5) → ((p2 ∧ True) ∨ p4))) → (p1 ∨ (p2 ∨ False))))) ∨ (((p3 → p3) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57657282471659303594824080368 : ((((p3 ∨ p3) ∨ p3) → (((p1 ∨ (p1 ∧ p4)) ∨ ((False ∨ False) ∨ (p3 → ((False ∧ (p2 → p5)) → (True ∧ p4))))) ∨ (p3 ∨ p4))) ∨ p5) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57005825459302057609592542993 : (((True → (p1 → p1)) ∧ (((p5 ∧ True) ∧ (p3 ∨ (((p4 → p1) ∨ ((p2 ∨ (p1 ∨ p2)) ∧ p4)) ∧ (True → p1)))) ∨ (True ∨ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_698479369492424361810152374757 : ((((((True ∨ ((p3 ∨ p4) ∧ p3)) ∧ p5) → ((p4 → p1) ∧ p3)) ∨ (((p2 ∨ True) ∧ (True → (p3 ∨ ((p4 → p4) ∧ False)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688082385872700684601076562242 : (((((p1 ∧ ((p3 ∨ p5) ∨ p4)) ∨ (p5 ∧ ((p1 ∨ True) ∨ (p4 → (p2 ∨ p5))))) ∧ ((p2 → (p5 ∧ True)) ∨ (p5 ∨ (p2 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317750513579330831544337824707 : (p4 ∨ ((((p1 ∧ p1) ∨ ((((p3 → False) → (p1 → (p5 ∨ (p1 → p5)))) → (p1 ∧ p2)) ∨ True)) ∨ ((False → (True ∧ p3)) ∧ p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133528248788387953098703022992 : ((((((p5 ∧ (p3 ∧ ((p1 ∧ ((p1 → False) → True)) ∨ p1))) ∨ p5) ∧ ((p5 → (p4 ∨ True)) ∨ p3)) ∧ p1) ∧ p2) ∨ (True ∨ (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111076816390747557064665450873 : (((((False ∨ p5) ∨ (((p2 → (True → False)) → (False → (p4 → p1))) ∧ p3)) → ((True ∧ (p3 ∧ p3)) ∧ (p3 ∨ p4))) ∧ p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40640692289506794234533573901 : ((((((p3 ∧ p1) ∧ (p2 ∨ (p2 ∨ (((((False → (p1 → p1)) ∧ p1) ∧ (False ∨ True)) ∨ (True ∧ p1)) ∨ p4)))) → p3) → p2) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325104041826168918205339691617 : (p5 ∨ ((p3 → p1) → (((((p3 → (False ∧ p5)) → p2) ∧ p5) ∨ (False → (p2 → (p1 ∧ (p5 ∨ False))))) ∨ (p5 → (False ∨ (p1 → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190109144305773525718086432315 : (((((p4 ∨ p1) ∧ False) ∧ ((p2 ∨ p5) → False)) ∧ p2) ∨ ((((p2 → ((p4 ∧ False) ∧ p5)) ∨ p5) → (p4 ∨ (p1 ∧ (p5 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_816880890037562484612644747301 : (((((((p1 ∨ p2) ∧ p1) → ((p4 ∨ ((p4 ∧ (((p1 → p3) → False) ∧ True)) ∨ p4)) ∨ (False ∨ (p4 → (p4 ∨ p2))))) → p2) ∧ p1) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∨ p2) ∧ p1) → ((p4 ∨ ((p4 ∧ (((p1 → p3) → False) ∧ True)) ∨ p4)) ∨ (False ∨ (p4 → (p4 ∨ p2))))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157970401129556012523847946998 : (((False ∧ (p4 ∧ (p3 → ((p1 ∧ p1) ∨ True)))) ∨ (((True ∧ p1) ∧ False) ∨ ((False ∨ False) → p2))) ∨ (p1 ∧ (((True → p2) → p1) → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596887413741591811774694747492 : ((((((p4 ∨ p2) ∨ ((p2 ∧ p2) → p1)) ∨ ((p2 ∨ ((p2 ∧ (p4 ∨ (((False → True) ∧ (True ∨ p5)) ∨ True))) ∧ p1)) → p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311172790417881441774074049627 : (p2 ∨ ((True ∨ p1) → ((((True ∧ ((p3 ∨ (False → ((p2 ∧ ((p4 ∨ p4) ∨ False)) ∧ (True ∨ (p5 ∨ True))))) ∨ p5)) ∧ p5) ∨ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_204176802096448153764015883014 : ((((p1 ∨ (p1 ∨ p5)) ∨ False) ∧ p2) ∨ ((((p5 → (p4 → True)) ∧ ((False ∧ (p1 → p1)) → p5)) ∧ (p1 ∨ (p3 ∧ False))) → (p5 → p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159155424958889639944213642894 : ((p1 → ((((((((p1 ∨ p5) ∨ True) ∧ p1) ∨ p5) ∧ ((p4 ∨ p4) → p5)) ∨ p2) ∧ False) ∨ p3)) ∨ ((True ∨ ((p1 ∨ p4) → True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64259231236316639983098434523 : ((False ∨ (p4 ∨ ((p3 → False) ∨ (((True ∨ (p2 ∧ False)) → (p5 ∨ (((p5 ∧ p1) → False) → (p5 ∧ ((p4 ∧ p2) ∨ True))))) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919674769918857857197891346987 : ((((p5 ∧ (((True ∨ p5) → ((p1 ∧ ((p4 → p1) ∧ False)) ∧ p2)) ∧ p5)) ∧ (((((False → True) → p2) ∨ p2) → (p3 ∨ p1)) ∨ p1)) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198344138324742872009888831442 : ((p2 ∧ (((p3 ∧ p1) ∨ p4) → (True ∨ p4))) ∨ (p1 → (((p5 → ((p5 → (p3 → p5)) → (False → ((p5 ∧ False) ∨ True)))) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351084476169405969581395301060 : (p4 → ((((((p1 ∨ p2) ∨ True) → p2) ∨ p3) ∧ (True ∧ (p4 ∧ ((True ∧ True) → (((True ∨ (p2 ∨ p2)) ∧ True) ∧ False))))) → (p1 ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h4.left
    let h15 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137441332407111783716870819391 : ((p4 ∧ (((p2 ∨ p4) → ((p3 ∨ p1) → ((p1 ∧ p3) ∧ (True → False)))) ∧ (p2 ∨ (p2 ∨ (p3 → (p4 ∨ p2)))))) ∨ (p1 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147309583489242341876256174761 : (((((p5 ∨ (False ∨ p4)) → (((p1 → True) ∧ ((True ∧ (p4 ∧ p2)) ∧ p2)) ∨ (p4 ∨ p4))) → p4) ∨ p3) ∨ ((p3 ∧ p5) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604376518506328178540622655627 : ((((True → ((p2 → p5) ∨ (((p1 ∨ (p3 → p2)) ∨ (p5 → (((p4 ∧ p5) → (p5 → p5)) ∧ ((False → p4) ∨ p3)))) ∧ p4))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32854552074169509626035261399 : ((p3 ∨ ((((True ∨ False) → (p5 → (p4 ∨ (True ∨ False)))) ∧ ((True ∧ (p2 → p5)) → ((p2 ∧ ((p4 → p4) ∨ False)) ∨ p4))) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37933256691958853041179280274 : ((((p4 ∧ ((((((p5 ∧ ((p1 → (True ∧ p4)) → False)) ∨ p4) → (False ∨ (p3 ∧ True))) ∨ True) ∧ p2) → p3)) ∧ (p4 ∨ p3)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300050761259535524028708232892 : (False ∨ ((((((p1 → ((p5 → (p5 ∧ ((p4 ∧ (p4 → p4)) ∨ p4))) ∧ p2)) → (False → p5)) ∧ (p4 ∨ p4)) ∨ False) ∧ p4) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64222015296066707156269455928 : ((False ∨ (p5 ∧ ((p2 ∧ (p3 ∧ ((False ∨ ((p5 ∧ p1) ∧ (p2 ∨ True))) ∧ (((p1 ∨ True) → ((p5 ∨ True) ∨ p1)) ∨ True)))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115689969109014632188373664007 : (((p4 ∨ (p5 ∨ (p1 ∧ (p1 ∨ False)))) ∨ (((((False → (p2 ∧ p2)) → p3) → p3) ∨ p1) ∨ (p1 ∧ (p2 ∨ (p1 ∧ False))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679904447020017581210740345041 : (((((((p4 → p1) ∧ ((((False → p2) ∨ p4) ∧ True) ∨ (((p4 ∨ p5) → p3) → p3))) ∨ p1) → p1) → (False ∨ (p4 ∨ (p2 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60376662478484700148788183889 : (((p3 → p1) → ((p3 → (True ∧ p4)) ∨ (p5 ∧ (p1 → ((((p5 ∧ (True ∧ p3)) ∨ p2) ∧ ((p4 → (p4 ∧ True)) ∧ False)) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47399393373235637662173732949 : (((True ∧ (((p3 → p1) ∧ (((p4 ∨ (((p4 → p1) → p2) → p5)) → p1) ∨ (p3 → p3))) → (p1 ∧ (p2 ∨ True)))) ∨ (False ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755168051060147903046559565861 : (((False ∧ (p3 → (((((False ∨ (p3 ∧ ((p4 ∧ False) → (p3 ∧ (p2 ∨ p1))))) ∧ (False ∨ (p1 → p1))) ∧ p3) → p1) ∧ (False → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214570174592546637028069093713 : (((p2 ∨ p1) ∧ (p5 ∧ p2)) ∨ ((p2 ∨ True) ∨ (((False ∧ (p1 ∨ (((p1 ∨ (p1 → (False ∨ False))) → p1) → (p5 ∧ False)))) → p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111978820085758249225368294414 : ((((False ∨ (p5 → (p4 ∧ (False ∨ p1)))) ∨ (((p3 → ((True ∧ True) ∧ (p5 → p1))) ∨ (p1 → (p3 ∨ p2))) → p2)) ∨ True) ∨ (False → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136351817452267984917312822398 : (((p1 → (p5 → (p1 ∧ p4))) ∧ ((p3 ∧ ((p3 ∧ ((False → (p2 → p5)) ∨ False)) ∧ (p4 ∨ True))) → (p2 ∧ p5))) ∨ ((True ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42393075090557521726132889964 : (((p4 ∧ ((p3 ∧ False) ∧ (((p4 ∨ ((p4 ∨ ((p4 → p4) ∨ (False → p3))) → p5)) ∧ p4) ∧ ((p4 ∧ p3) ∧ (p5 ∧ p4))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110966190572823937414470555958 : ((((p4 ∧ (((p5 ∧ (((False ∧ True) → (True ∧ p2)) ∨ ((p3 → False) ∧ (p2 → p5)))) → p1) ∨ p1)) ∨ (False → p3)) ∧ False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111056371243563859883102508343 : ((((False → (((((p3 → (True ∧ (True → (p1 ∨ p2)))) ∨ p5) ∧ p2) ∧ p1) ∧ p2)) → (((p5 ∨ p4) ∨ p5) → p3)) ∧ False) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171587069140587287855862679126 : (((((p5 ∨ p5) ∧ ((p4 ∧ False) ∨ (p1 ∨ p3))) ∧ ((p5 → p5) → p3)) ∨ p3) ∨ (((p3 → p3) ∧ (((p5 ∧ p5) → p4) ∧ p4)) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241649533694138904731577616044 : ((False → p5) ∧ (((False ∧ (((((p1 → p1) → True) → p4) ∧ ((p5 ∧ (p5 ∨ p1)) → p1)) ∧ (True ∧ (p1 → p5)))) ∨ True) ∨ (p2 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304119758820216491045745377502 : (p1 ∨ ((p4 → (((True → (((p3 ∨ (p5 ∧ (((False → False) → False) ∨ (False ∧ p3)))) ∧ p1) ∧ (True → p2))) ∧ p4) ∨ (p2 → p4))) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318877961471746704969332893980 : (p4 ∨ (((False ∧ ((False ∨ p5) → (p1 ∨ (p3 ∨ p5)))) ∨ (p5 → (False ∨ (((p5 ∧ p3) ∨ (p5 → p4)) ∨ True)))) ∨ ((p2 ∧ p2) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_321037570777408346688376279205 : (p4 ∨ (False ∨ (True → (p4 ∨ ((((p3 ∨ ((((((p2 ∧ True) ∨ p4) → p4) ∧ False) → p5) ∧ p2)) → p4) ∨ ((p5 ∧ False) → p2)) ∧ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350965278459734914410872249285 : (p4 → ((((((True → p2) ∨ (p4 ∨ True)) ∧ p1) ∧ p4) → (((p3 ∧ (False ∧ (True ∧ p2))) ∨ (True ∧ (p1 ∧ p4))) ∧ p1)) ∨ (p2 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h4
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180490240287089011422749018062 : ((((True ∨ ((p3 → p5) ∨ p2)) ∧ (p1 ∨ p1)) ∧ ((p4 ∨ p1) ∨ p3)) → ((((p3 ∧ p4) ∨ ((p5 ∨ p3) ∨ True)) ∨ p3) ∨ (p2 ∧ p5))) := by
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
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
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
        case inr h10 =>
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
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
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
        case inr h15 =>
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
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
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
          case inr h22 =>
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
        case inr h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
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
          case inr h27 =>
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
        case inr h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h32 =>
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
          case inr h33 =>
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
        case inr h34 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h34
      case inr h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
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
          case inr h38 =>
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
        case inr h39 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323192576464271768465278201607 : (p5 ∨ ((((p4 ∧ (((p2 ∨ p4) ∨ p5) → p5)) ∧ (p1 → (((p2 ∧ (True ∨ p4)) → (p4 ∧ (p4 ∨ p4))) ∧ p2))) → p5) ∨ (p4 ∨ p3))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∨ p4) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662964315496459491746956094468 : (((((p3 → (True → False)) ∨ ((p5 ∨ ((((p4 ∧ (p2 ∨ p1)) ∧ p3) → p3) → p5)) ∨ ((p5 ∧ (p5 → p1)) ∨ p4))) → (p2 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54728067310931050101681194973 : ((((p4 → (p4 → p3)) ∧ ((p1 ∨ p1) ∨ p2)) → (p2 → (p4 ∨ ((p5 ∧ (p3 ∧ (((p3 ∨ False) → (p2 ∧ p3)) ∨ p4))) ∨ True)))) ∨ p1) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593441013571246835644123400878 : (((((((((p4 ∧ False) ∨ (p2 ∨ p3)) → (p3 ∧ False)) → p2) ∧ ((p5 → p2) ∨ ((p4 ∧ p2) ∨ True))) → (p1 → (p1 → p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388045118984635035842294402712 : ((((((p1 ∧ p4) ∧ ((p2 ∧ ((True ∧ False) → (p3 → ((True → True) → p3)))) ∧ (p3 → p1))) ∧ ((p5 → p2) ∨ (p2 → True))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_190905187689258190571931693222 : (((p5 ∨ (p1 ∨ ((p5 ∨ False) ∧ p5))) → (False ∧ False)) ∨ (((p4 ∨ p2) → True) → (((True ∨ (p4 → ((p5 ∨ p5) ∨ p3))) ∨ p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786668214603591091016630726544 : (((p4 ∨ ((p3 ∧ ((False ∨ (False ∧ p3)) ∨ p4)) ∧ (((((p2 ∧ p5) → p4) ∨ (False → p5)) ∧ (p5 ∨ False)) ∨ ((p2 ∧ False) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299139691732389489705510507203 : (False ∨ ((((p5 → ((True ∧ ((p4 → p1) ∧ ((p4 → False) ∨ p3))) ∨ True)) → ((p5 ∧ False) ∧ (((p2 → p3) ∨ p2) → p5))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46998812439390422984633119489 : ((((((p1 → (True ∧ p4)) ∧ p3) → ((False ∨ False) ∨ ((p4 ∨ (False ∧ (p2 → p1))) ∧ (True → (True ∨ p5))))) → p3) ∨ (p2 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177735320156700985634851573791 : ((((False ∧ (False ∨ p3)) ∧ (p3 ∨ ((p4 ∧ p5) ∧ (p1 ∨ False)))) ∧ p1) ∨ (True ∨ (True → ((p4 → (p4 ∧ ((True → p1) → p5))) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253860789486880234688876558039 : ((p1 ∧ p3) → ((True → ((p5 ∨ (((p5 ∨ p5) → p1) → ((((p3 ∨ p3) ∧ True) ∧ False) ∧ (p2 ∧ p5)))) ∨ p3)) ∨ ((p4 → True) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60539758263721777850991901832 : ((True ∧ (((p2 ∨ ((p4 ∨ (p4 ∨ p4)) → (False ∨ p3))) ∧ ((p3 ∨ (False → ((p3 → p2) ∧ (True ∨ True)))) ∨ (p4 → p2))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229526894232194621211149528297 : ((p2 → (p4 ∨ False)) ∨ (p4 ∨ (((p2 → p4) ∧ (p5 ∨ ((p2 ∧ False) ∨ (((p4 → p4) ∨ p2) ∧ ((False → (False ∧ p5)) ∧ p2))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58774752404424985348101755087 : (((p4 → p3) ∧ (False ∧ (True → ((((p3 ∧ False) ∧ p5) ∨ (((p5 ∧ (((False → p1) → (False ∧ False)) ∧ p2)) ∨ p3) → p1)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



