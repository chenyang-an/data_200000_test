variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712133948737705693537241575105 : (((((p2 → ((p4 → False) ∨ p3)) ∨ p4) ∨ (p5 ∧ ((((p1 ∨ p3) ∧ ((p1 ∨ p5) → (((p4 → True) ∨ p4) ∨ False))) → p4) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176562894984872811669473369857 : (((p5 ∨ ((p2 → (p2 → True)) ∨ p1)) ∨ (((p4 ∨ p3) ∧ True) ∧ p1)) ∧ (((False → (((p1 → (True ∨ True)) ∧ p3) ∧ True)) → False) ∨ True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40188095872387071143164204813 : (((((p1 ∧ (p4 ∧ True)) ∧ (((p1 → ((p2 ∨ p1) ∧ (((p3 → True) ∨ True) → ((p3 → p4) → p1)))) ∧ True) ∨ False)) ∧ p3) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204657878113914444926648163913 : (((p4 ∧ ((p2 → p1) ∨ p4)) ∨ False) ∨ ((True → False) ∨ (((p3 ∧ ((False ∧ False) ∧ p4)) ∨ (True ∨ (p2 ∧ p2))) ∨ ((False → p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64014653204783431918257727719 : ((False ∨ ((((True → ((((p3 ∨ p4) → (p1 ∨ p2)) → p1) → p3)) → (p3 → False)) ∨ ((True ∨ (False → True)) ∨ p1)) ∨ (False ∧ p3))) ∨ p5) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136243458073098383734928983549 : (((p1 ∧ (p5 ∧ ((False ∨ p3) ∧ p2))) ∨ (False ∨ ((p3 → (((False ∨ False) ∨ True) ∨ False)) ∨ (False ∨ (True ∨ p2))))) ∨ ((p4 ∧ p4) → p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347852626903793291029949071903 : (p3 → ((p2 ∧ (p5 ∨ p3)) → ((p3 ∧ ((p5 ∧ (True ∧ ((p4 ∧ ((((True ∧ p1) → p2) → False) ∨ p5)) ∧ p2))) ∧ p1)) ∨ (p1 → p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614111618186425793869546786276 : (((((p1 → ((p5 ∨ (((p5 ∨ ((p4 ∨ p3) ∧ p3)) ∨ p1) ∨ (((p5 ∧ p4) ∧ False) ∨ True))) ∧ p1)) ∨ ((p3 ∨ p1) → False)) ∨ p2) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69351683889549766782364870473 : ((p5 → (p3 ∨ (((p4 ∧ ((False ∨ (((p1 ∨ p4) → (p4 ∨ ((p4 ∨ p4) → p1))) ∧ p3)) → ((p2 ∧ p4) ∨ p4))) → p1) ∨ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313337761755298250995137149451 : (p3 ∨ ((True → (((((False → p2) ∧ False) → (((p4 ∧ p1) ∨ (p1 → p2)) ∨ ((False ∧ p5) → (p2 ∧ p5)))) → p5) ∨ (False → True))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228422406174062091115712817628 : ((False ∨ (p3 ∧ p4)) ∨ (p2 → (((True ∨ (((((True → False) ∨ (True ∧ False)) ∧ p5) → (p5 ∧ (False ∧ (p4 ∨ p3)))) ∨ True)) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801049197747037449391216454657 : (((p2 → ((False ∨ ((p4 → p2) → (((p5 ∨ (p1 → False)) → p2) ∧ (False ∧ (False ∨ ((p2 → p5) ∧ p3)))))) ∨ ((p3 ∨ True) ∨ False))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115221993265193201486116858024 : (((p5 → ((p4 → (p5 → p1)) ∧ (p1 → (p3 → p4)))) ∧ ((True → ((p3 → (False ∧ p2)) ∨ ((p1 → p2) → p3))) → False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351684919883898879206578865502 : (p4 → ((p1 → ((p4 ∧ ((((p2 ∧ (True → p5)) ∧ p2) ∨ (p5 ∨ p5)) → p2)) ∧ p5)) → (((p3 → (True ∧ True)) → (True → p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54720382668110828838152616897 : ((((p2 → ((p1 ∧ p3) ∨ p1)) → (p1 → p3)) → (p5 → (((p5 ∧ (((p5 ∨ p4) ∧ (False → (p4 ∧ p3))) ∧ p4)) → False) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_113118228667496850342676018314 : (((False → (p4 ∧ (((p1 ∨ ((True → (p5 → p4)) ∧ (p4 → p5))) → (True ∧ p4)) → ((True ∧ p2) → (p1 ∨ p5))))) → p2) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57238270435993751276599820280 : ((((p1 ∧ p3) → False) ∨ ((p1 ∧ (p5 ∧ p1)) → ((p4 ∨ (((p5 ∨ p4) ∧ (p3 ∧ (True ∨ p1))) ∨ ((p4 ∨ p3) ∧ p3))) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636860238740948161843293999049 : ((((((True ∨ p5) ∧ (p3 → (p5 ∨ (False ∨ (((p4 ∧ p1) ∧ p3) → p1))))) → (p3 → ((p1 ∨ p5) → ((True ∧ p4) ∨ p5)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702877430176931107564730265428 : ((((((p2 → (p4 → p1)) ∨ p4) → ((p2 ∧ p1) ∨ p4)) ∨ (((True ∧ (p4 ∧ (p5 ∧ (True → p2)))) ∧ (p3 → False)) ∨ (p5 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135577372386305323384620846900 : (((((((p4 ∨ p5) → True) → (True → p4)) → ((p5 ∧ p2) ∧ (False ∨ p3))) ∨ False) ∨ (((p5 ∨ p4) → True) ∨ p5)) ∨ (p1 ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136856864782141870734393677512 : (((p5 ∧ True) ∨ ((p5 → (p2 → (p4 ∨ (p3 ∨ ((p4 → ((p2 ∨ p5) ∧ False)) → (p3 ∨ (True ∨ p3))))))) → p3)) ∨ ((p2 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347865134897360477087972424941 : (p3 → ((p3 ∨ (p4 ∨ p2)) → (((p2 → ((p5 ∨ p1) ∨ ((((p4 → (p2 ∧ False)) ∧ p5) → p1) → p3))) → ((p5 → p2) ∨ p1)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148742939264446996900871644518 : (((((p5 ∨ p1) ∧ p1) ∨ (p2 → p1)) ∧ (((True ∨ False) ∨ True) → (p4 ∧ (p4 → (p4 ∨ (True ∧ p3)))))) ∨ (True → ((False ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624902622732466186261847551312 : ((((p5 ∨ (((True ∨ (p5 ∧ p2)) ∧ True) → ((((p3 → p5) ∧ p5) → (p4 ∨ ((((p4 → p4) ∧ p4) ∨ False) ∧ p4))) ∨ True))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_113603397830819931582804893725 : (((p1 ∨ (True ∧ ((((False ∨ p1) ∨ ((True ∨ ((True → p1) ∨ p2)) ∨ (p4 ∧ p1))) ∧ p4) ∧ (p2 → False)))) ∨ (False → p4)) ∨ (True → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117498647697933721791598757421 : ((p2 ∧ ((((((p4 ∨ p5) ∧ ((False → ((p4 → p4) ∨ p2)) ∧ (True ∨ p2))) ∧ (True → (p5 ∧ p5))) ∧ p3) ∨ p3) ∧ p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919645909516352162409669441422 : ((((p3 ∧ (True ∧ ((True ∨ ((False ∨ p2) → ((p2 ∧ p4) → p2))) ∧ True))) ∧ ((False ∨ (p3 → (p1 → ((False ∧ p4) ∨ True)))) → p4)) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (False ∨ (p3 → (p1 → ((False ∧ p4) ∨ True)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h16 : (False ∨ (p3 → (p1 → ((False ∧ p4) ∨ True)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h16
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61569345271780982422533446126 : ((p1 ∧ (((p2 → ((p2 ∧ True) ∧ True)) ∨ p2) → (((False → (False ∧ ((True → (p3 → (True ∨ (p3 ∧ False)))) → p3))) ∧ False) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149043965053057884360750899184 : (((p2 ∨ (p3 → False)) ∨ ((p5 → p3) ∧ (p2 ∨ (((p5 ∨ ((False ∧ (p4 ∧ True)) ∨ True)) ∧ p4) ∨ p3)))) ∨ ((p2 → (p1 → p1)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610975999455697260691057923808 : ((((((((p1 ∧ (p1 ∧ False)) ∨ (True → p5)) ∧ p3) ∨ (p2 ∨ ((p4 ∨ ((p1 → p2) ∨ (p3 → (False ∧ p5)))) ∧ p1))) → False) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137711344511049807649234263527 : ((p1 ∨ ((False ∨ ((p4 ∨ (True ∧ p5)) ∧ p3)) ∧ (((((p1 ∧ p5) → False) ∧ False) ∧ True) ∨ ((p4 ∧ True) ∧ True)))) ∨ ((True → False) → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174561877810556080740920999488 : ((((p5 ∧ p4) ∧ (p5 ∨ p5)) ∧ (((False ∨ (p1 → (p3 → False))) ∨ p1) ∨ True)) → ((p2 ∨ (((True → (p1 ∧ p4)) → p4) ∧ True)) ∨ p2)) := by
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
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h7
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h23
          -- One of the premise coincides with the conclusion.
          exact h7
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h26 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h7
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345712124090706230904697580339 : (p3 → ((p1 → (((p2 → p5) ∨ p1) → (((True → (p5 → True)) ∨ ((p5 ∧ (((True ∨ (p4 → p4)) ∧ p2) ∨ True)) ∨ True)) → p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134763497327844357425963717968 : ((((p5 ∨ p3) → (p2 ∨ ((p2 ∨ (True ∨ ((p5 ∧ (p1 ∨ (p2 ∧ p5))) ∧ True))) → ((True ∧ p5) → p5)))) → p2) ∨ ((True ∧ False) → p4)) := by
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
theorem thm_5_vars_159227842827610807057091944443 : ((p3 → ((((((False → p1) ∧ (True ∧ False)) ∨ True) → (p4 ∨ (p2 → p2))) → (p5 ∧ p5)) ∧ p1)) ∨ (p1 → ((p3 ∧ p1) ∨ (p2 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336218958453220599973688863582 : (p1 → (((((((p3 → (p5 ∧ ((p2 ∧ False) ∧ p2))) ∨ (p5 → p4)) ∨ p4) → p5) ∧ ((p2 ∨ p3) → p2)) ∧ ((True ∧ p4) ∧ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339687707158077510172413602432 : (p1 → (p3 ∨ ((False ∨ (False → (p1 ∧ (False → ((p5 → p4) ∧ True))))) → ((p4 ∨ (p4 → p4)) ∨ (((True ∧ (p1 → p4)) → p4) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_570819648487048558909856565139 : (((p1 → ((((p5 ∧ p2) ∧ (((p4 ∧ p5) ∧ (False → True)) ∨ p1)) ∨ ((p5 → ((p2 → ((p5 ∧ p3) ∧ p5)) ∨ False)) ∨ p3)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46906473837440298363919587440 : ((((((((p3 → p1) → True) → ((p2 ∨ False) ∧ ((p2 ∨ (p5 ∨ p4)) ∨ p3))) → p4) ∨ ((p3 → p1) ∧ p1)) ∨ p5) ∨ (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300684014447639050660404655130 : (False ∨ (((p4 ∧ (p5 ∨ True)) ∨ (((((False ∨ ((p4 ∨ True) → True)) ∧ p1) → False) → p4) ∧ True)) ∨ ((True ∨ (p2 ∧ (False ∨ p4))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304751118808253716495387860306 : (p1 ∨ (((p5 → True) ∧ ((p4 ∧ ((p1 → p4) ∧ p3)) → ((p4 → ((p4 ∨ (p4 → p5)) ∧ (p4 ∨ True))) ∧ (p5 ∨ p5)))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119211157125369328469676693115 : ((p2 → ((p3 → ((((p5 ∧ p1) ∨ (False → p5)) ∧ True) → p4)) → (((p3 → p3) → False) → (((False ∧ False) ∨ p3) ∧ p2)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44301558269682799093638150927 : ((((p3 ∨ ((((p2 ∧ p1) ∧ True) ∨ ((False ∨ (p5 → True)) → p3)) ∧ (True ∧ False))) ∧ (p5 → (p1 ∧ (p2 → (True ∧ p2))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655658164367840744104228295502 : ((((((((p4 ∨ p3) ∨ ((p1 ∧ (True → p1)) → (p2 ∨ (p5 → (p3 ∨ p1))))) ∨ p5) → False) ∧ ((True → True) ∧ p1)) ∨ (True ∨ False)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_225418779400055353635761127387 : (((p3 ∨ p1) ∧ p3) ∨ (p1 ∨ (p1 ∨ ((p3 → (p3 → (True ∨ (p5 → ((p3 → p5) ∨ ((p5 ∧ p3) ∨ ((True → p4) → p2))))))) ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184944930526367966785172076254 : ((((p4 ∨ p2) ∧ p2) → (((True ∧ p5) ∨ (p5 ∨ p4)) ∨ p2)) ∨ (p4 ∧ (p3 → ((p1 ∨ True) ∨ (p5 ∧ ((p3 ∨ (False ∨ p5)) ∨ p1)))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113695646619366189170995965121 : ((((((p1 ∨ p4) ∨ p4) → ((((((p1 → (False → p3)) ∨ (p1 ∧ p5)) ∨ False) ∨ p2) → p4) ∨ p2)) → p5) → (p4 ∧ p4)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305421169271440322871581087676 : (p1 ∨ ((True → ((p2 ∧ ((p4 ∨ (((p5 → (p1 → p1)) → False) ∧ True)) → p1)) → p1)) ∨ ((p5 ∨ (((p5 ∧ p4) ∨ p1) ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113615547908247719417196919107 : (((p5 ∨ (((False ∨ True) ∨ p3) → (p4 ∨ ((p4 ∧ (p3 → ((((p4 ∨ p5) ∧ False) ∧ p2) ∧ True))) ∨ p2)))) ∨ (False → p5)) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46158314782622502820798512963 : (((((((((True → (False ∧ p4)) ∧ p3) ∨ (False → (False ∨ p2))) ∨ True) ∨ (p2 ∧ p2)) → (p2 ∨ (p4 → True))) → p5) ∧ (p3 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116610410876750515923957506580 : (((True → p3) ∧ ((p5 ∨ ((p2 ∨ p4) → (False → p5))) ∧ (p5 ∧ ((p5 ∧ True) ∧ ((False ∨ True) → ((p4 ∨ False) ∨ p1)))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45981342036094158358017923780 : (((((((p2 → ((((((p3 → p1) → (p2 ∨ False)) ∨ (p5 ∧ p1)) → True) ∨ p4) → p2)) → False) ∨ True) ∨ p1) ∧ False) ∧ (p3 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229095583227975058043646145524 : ((p5 ∨ (p4 → p2)) ∨ (p2 → (p5 → ((p4 → p1) ∨ (((p4 → p1) ∧ (p1 ∧ (((p3 ∨ False) ∨ ((p4 ∨ p4) ∨ True)) → p3))) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68453853048271677683863404623 : ((p3 → (p1 ∧ ((True ∨ p1) ∧ (((p1 → p3) → (p2 ∧ ((True ∧ p5) ∨ ((False ∨ p1) → (p5 → (p3 ∧ p1)))))) ∨ (p2 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191065684313501297512660809396 : (((p2 ∨ ((True ∨ True) ∨ p5)) → ((p5 ∧ p5) ∨ p1)) ∨ (p1 → (p3 ∨ ((p3 → p3) ∧ (((p2 ∧ (p5 ∨ p2)) → (p1 ∧ p5)) → True))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157453925376985076951356747053 : ((((((((False ∧ False) ∧ p2) → (True ∧ False)) ∨ (p1 ∧ (True ∧ p2))) → False) ∧ p5) ∨ (False → p5)) ∨ (((p1 ∨ p3) ∨ p2) ∧ (p2 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135724194015948111538246547961 : (((((p3 ∨ ((True ∧ p3) ∧ (False ∨ p3))) ∨ (p3 ∧ (p2 ∧ p4))) ∧ p4) ∨ (True ∧ (False → (p5 ∧ (False ∨ False))))) ∨ ((p1 ∧ p5) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42665689989579771520096403417 : (((p4 ∨ ((p4 ∨ ((p1 ∨ p2) ∨ p5)) ∧ (((p3 ∧ (p3 → (p4 ∧ p2))) ∨ (p4 ∧ ((p5 → (p2 → p5)) → False))) → p1))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116431809970455521944759485398 : (((False → (p2 ∨ p1)) → (((p5 ∧ (p5 ∨ (((p5 ∧ (True ∧ (p1 ∧ (p2 ∨ False)))) → (p5 ∨ False)) → p1))) → p2) ∧ False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117343736831615997555808019365 : ((False ∧ ((p1 ∧ p5) → ((p5 ∨ ((((((p3 ∨ (p5 ∨ p5)) ∨ p1) ∧ (p5 ∨ p2)) ∧ (p4 ∧ p3)) ∨ p1) ∨ True)) → p3))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50092118762135959203997025325 : (((p2 ∧ (p4 ∧ (((p4 → True) ∧ ((True ∨ p1) ∨ p4)) → ((p1 → p4) → (p1 → (p4 ∧ p4)))))) ∧ (p5 → ((True → p5) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325137831829180039641818212925 : (p5 ∨ (True ∧ (((p1 ∨ ((p4 → (p1 ∧ (p2 → (False ∨ ((p2 ∨ True) → (((p4 → p3) → p5) ∨ p2)))))) → p1)) → p2) ∨ (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801409723417835114813697370673 : (((p2 → ((((p4 ∧ p4) ∨ p4) ∧ (p5 → ((p3 ∨ p2) → p3))) ∧ (((p4 ∧ ((((p4 → p1) ∨ p2) ∨ p4) ∧ p2)) ∨ p1) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650578616995535036315515073394 : (((((((p1 → False) → (False ∧ p1)) → (True ∧ ((True ∧ p2) ∧ p4))) → ((p2 ∨ p5) → (True ∧ ((True ∨ p3) ∧ False)))) ∧ (False ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713897338472301380864296717545 : (((((True ∧ (p3 → (False ∧ True))) ∨ p5) → (((p4 ∧ (p3 ∧ p2)) ∨ p4) ∨ ((((p5 ∧ p5) ∨ p1) → True) ∨ ((False ∨ True) ∨ p2)))) ∨ p5) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112917167931874210970831861532 : ((((False → p5) ∨ (p3 ∧ (p1 → (((((False → p1) ∧ (p5 ∨ p3)) ∨ p3) ∧ ((p2 ∨ (p2 → p1)) → p5)) ∧ p2)))) → p4) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694168328648057770173062262685 : (((((p1 → ((True ∧ False) ∨ (p4 ∧ p3))) ∨ (p4 ∧ (False ∧ (p5 → False)))) ∨ (True ∨ (p3 ∨ (((p3 ∨ p3) → p5) → (p2 → p3))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_149145080294227655108369481826 : (((True ∨ p3) ∧ ((p3 ∨ (((True ∧ (p5 → (True ∨ p5))) → p5) ∨ False)) ∧ (((p1 ∧ False) ∧ p2) ∧ p5))) ∨ (((False ∧ True) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38659674197658445852481263283 : ((((p1 ∨ (p1 ∨ ((p4 ∧ (p5 → p3)) → p4))) → (((p2 ∧ (True ∧ (True → (p3 → (p5 ∧ p4))))) → p2) → (p2 ∧ p3))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167552097337700230744656516253 : (((((((p1 ∧ (False → p5)) → p3) ∧ (p1 ∨ (p1 ∨ False))) → p1) ∨ True) ∨ (False ∨ False)) → ((True → p4) → (p3 ∨ (p4 → (True ∧ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60552442068068238394064594776 : ((True ∧ ((p1 ∨ (((p4 ∨ ((p1 ∨ p3) ∧ p2)) ∧ (True ∧ (((p2 → True) ∨ (True ∧ (p1 → (p2 → p4)))) ∧ True))) ∧ True)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605925729600125495072055736619 : ((((p5 → (((((((p4 → (((p2 ∧ p4) → p1) → p4)) ∨ (p4 ∧ p2)) → True) → True) → (p3 ∨ p1)) → p4) ∨ (False ∧ p4))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156820314769607780110004129658 : (((p3 ∨ (True → ((((((p3 ∨ p2) ∨ p4) → True) ∧ p2) ∨ p2) ∨ ((p1 ∨ p4) ∧ p3)))) ∧ p5) ∨ ((p4 ∨ (p4 ∨ False)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115781875283521843477849418798 : (((((False → p2) → False) ∧ p5) ∧ ((((p1 → p3) → (p5 ∧ (p4 → (False ∧ True)))) ∨ p3) ∨ ((p3 ∨ p3) ∧ (p2 ∧ False)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731023945176712027000667843770 : ((((False ∨ (p1 → p5)) → ((((((p4 ∧ False) → p1) → ((p3 ∧ p2) → (p2 → p5))) ∧ (False ∧ p4)) → ((p2 → p5) ∧ False)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245429075911516699664827053901 : ((p2 ∧ p4) ∨ ((p4 → ((p5 → ((p1 ∧ p2) ∧ p2)) → p4)) → ((True → (((True → p4) ∧ (False ∧ p2)) ∧ True)) → ((p3 → p3) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586683158630626730746710745192 : (((((True ∧ (((((p3 → (p2 ∧ p3)) ∧ p3) → p5) ∧ (((p1 → p1) → (p4 → p3)) ∧ p5)) ∧ (p1 ∧ (True ∨ False)))) ∧ p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801997421793629831769295166101 : (((p2 → ((p2 ∧ p5) → (((True ∧ (p1 ∧ (((p2 ∨ p2) → True) ∨ (p4 ∨ ((False → (p3 ∨ (False → p1))) → p5))))) → False) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259795738355111441116798508659 : ((p1 → p3) → ((((((p4 → (p3 ∧ p4)) → ((((p1 ∧ ((True ∧ p5) ∨ False)) ∧ True) ∧ (p5 ∧ False)) ∧ p4)) ∨ False) ∨ p1) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47894577540865188793579610110 : (((((p5 → True) ∨ ((p2 ∧ ((False → ((p3 ∧ False) → ((True ∨ p4) → (False → p2)))) ∧ p1)) ∨ p4)) ∨ (p4 → p5)) → (False ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51372336461185972615082164025 : ((((((False → ((False → True) → ((p4 ∨ True) ∧ p2))) ∧ (False → (p3 ∨ p1))) ∧ p1) ∨ True) → (((p2 ∨ (p4 ∨ True)) ∨ p5) ∨ True)) ∨ False) := by
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
theorem thm_5_vars_39751456723043606584489199425 : (((True → ((((False ∨ (p3 → (False → ((p5 ∨ (p1 → p3)) ∨ p5)))) ∨ p4) ∧ ((p5 ∧ p2) ∨ (p2 ∧ (p2 ∨ p1)))) ∨ False)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316367269998477050681062252571 : (p3 ∨ (False ∨ ((((p2 ∨ ((p5 → (p4 ∧ False)) → False)) → p4) ∨ (((True → ((((p4 → p2) → p1) → True) ∧ p5)) ∨ p2) ∨ True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186680528282321022033866899001 : (((True ∨ ((p4 → p4) ∨ (False → False))) ∧ ((True ∧ p3) ∧ p2)) → (((p2 ∨ p2) ∧ p3) ∧ ((p2 ∧ (p5 ∨ (p1 ∧ True))) ∨ (p5 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h21.left
      let h30 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h21.left
      let h35 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- One of the premise coincides with the conclusion.
      exact h37
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h39.left
    let h42 := h39.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h42
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h39.left
      let h48 := h39.right
      -- Conjunctions on the left can always be decomposed.
      let h49 := h47.left
      let h50 := h47.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h48
    case inr h51 =>
      -- Conjunctions on the left can always be decomposed.
      let h52 := h39.left
      let h53 := h39.right
      -- Conjunctions on the left can always be decomposed.
      let h54 := h52.left
      let h55 := h52.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215387054694972758725214986979 : ((p2 ∧ (p2 ∧ (p1 ∧ p5))) ∨ ((((p3 → (p3 ∧ True)) ∧ p3) ∧ ((False ∨ p2) ∧ ((False ∧ (p1 → (p1 ∨ True))) → True))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809002803039217117150416625966 : (((p5 → ((((p4 ∧ p3) ∧ p2) ∧ (((p5 → True) ∧ (p5 → (p1 → ((p4 → True) ∨ (p5 ∧ (True ∧ (p1 → False))))))) → p4)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48551757674243623166105175444 : (((((p4 ∧ ((p1 → ((((p3 ∨ True) ∨ False) ∨ p4) → ((p1 ∨ p4) ∧ p2))) → (p1 → p5))) → p3) → p5) ∧ ((p2 ∧ p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135260542594496198974597933645 : (((p2 ∧ (False ∨ (((p4 → False) ∧ True) ∧ (((p3 → True) ∨ (p3 ∨ (p4 ∧ (p2 → p4)))) ∨ p4)))) → (True ∧ p3)) ∨ ((False ∧ p2) → p4)) := by
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
theorem thm_5_vars_354980086640769848656789287008 : (p5 → ((p5 → ((p2 → (p4 ∨ (p1 → (p2 → (p2 ∧ p2))))) ∧ ((((p3 ∧ ((p1 ∧ False) ∧ (True ∨ p5))) → p3) ∨ False) → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339736694603111741010718555894 : (p1 → (p4 ∨ ((p4 ∨ (((p1 → ((((p2 ∧ False) → p2) ∧ (p5 ∨ ((True ∨ (p2 ∨ p1)) ∧ p3))) ∨ p5)) ∨ p1) ∨ p5)) ∨ (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49301753769695298640214898385 : (((False ∨ ((p2 ∧ p4) ∧ (((p1 ∧ p1) ∨ (p2 ∧ (p3 ∨ p2))) ∧ (p1 ∧ (False → ((False ∨ p3) ∨ p2)))))) ∨ (p2 → (p1 → p1))) ∨ p2) := by
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
theorem thm_5_vars_149094188095537883315798493004 : (((True ∨ (p3 → True)) → (((((p3 ∧ False) ∧ p1) ∨ (p4 ∨ p4)) ∨ False) ∧ (((p1 ∧ p4) ∧ p5) → p2))) ∨ ((p2 ∨ p1) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703865567094447891014712704741 : ((((((p4 ∨ ((p1 ∨ p4) → False)) → (p3 ∨ True)) ∨ True) → (p5 → ((p2 ∨ p3) ∨ ((False ∧ ((p1 ∧ True) ∧ (p2 ∧ p2))) ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42548285410182914117847280448 : (((p1 ∨ (((p5 ∧ True) ∧ (p2 ∧ p4)) → ((p4 → ((p4 → (p4 ∨ p5)) → p1)) ∧ ((True → p4) ∨ (p4 → (True → p4)))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41434719761837492927642853589 : ((((((False → (True ∨ (p3 ∧ p2))) ∧ True) ∨ (((False ∨ True) → False) ∨ True)) → ((p2 → ((False ∨ p4) ∧ p4)) ∧ (True → False))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1946054255229537428528427599 : ((((((p1 ∨ True) ∧ (((p1 ∨ ((True ∧ False) → p4)) ∧ False) ∧ (p2 ∨ p1))) ∨ p1) → p5) → p2) ∨ (p4 ∨ (p5 ∨ (p3 → p3)))) := by
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
theorem thm_5_vars_351423019292713875807423914732 : (p4 → ((False ∨ (((p4 ∨ (False → p2)) → False) ∨ ((((p5 ∨ True) ∨ (p2 ∨ p1)) ∨ (True ∧ False)) → True))) ∨ (((p4 ∨ p2) → p5) ∧ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707718681701545555666038978788 : (((((p5 ∧ p5) → ((p2 ∨ (False ∨ False)) ∨ False)) ∨ ((((p1 ∨ False) ∧ p4) ∧ (p2 → p5)) → ((p4 ∧ (p5 → (True ∧ True))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50910122571126652812234255398 : (((((p1 ∧ (p4 ∨ p4)) ∧ (p3 ∧ (p2 ∨ ((p5 ∧ p5) ∨ (p2 → True))))) ∨ (p5 ∧ p4)) ∧ ((True → ((p2 → p3) ∨ p3)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134541635159113142714316619517 : (((((True → ((p4 → False) ∨ ((p5 ∧ False) ∧ ((p2 ∨ p4) ∧ p4)))) ∧ ((p4 ∨ p5) ∧ (p3 → p2))) → p2) → p1) ∨ ((p1 → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



