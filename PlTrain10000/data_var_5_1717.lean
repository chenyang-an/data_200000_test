variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653963748584823657769768137809 : (((((False ∧ (p4 → ((p2 ∨ ((True ∧ (p1 ∧ True)) ∧ (((p1 → p2) ∧ (p4 → p3)) ∧ (False → False)))) ∨ p3))) ∧ p4) ∨ (True ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_113490981732283161433071023501 : ((((p3 → (((False → p1) → p3) → ((True ∨ ((p5 ∨ False) ∧ p3)) → (p1 ∧ (p1 ∧ False))))) → (p2 ∨ p2)) ∨ (True ∨ p1)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109536582553958405374611683930 : ((p3 ∨ ((p2 → (p2 → ((p5 → (p4 ∧ p2)) ∨ (((p3 ∧ p3) ∨ ((p5 ∧ (p3 ∨ p1)) ∨ (p1 ∨ p4))) → False)))) ∨ True)) ∧ (p4 → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678380559888636110882004028687 : (((((((p2 → p4) → True) ∧ (p5 → p2)) → ((p3 ∧ True) ∧ ((p5 → (False ∧ (p3 ∨ p3))) → False))) ∨ (p3 ∧ (p4 ∧ (p3 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44477867299306450454132322563 : (((((p4 ∨ True) ∨ (((p3 ∨ (p2 → (False → False))) → p5) ∨ True)) → (((p4 → (p5 ∨ ((p1 ∨ p4) ∧ p4))) ∨ p4) ∧ False)) → p3) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ True) ∨ (((p3 ∨ (p2 → (False → False))) → p5) ∨ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47095624284470878051854554162 : ((((p2 → ((p5 → ((p4 ∨ p5) ∨ p4)) → (p1 → (((((p1 ∧ p4) ∨ p4) → p1) ∨ p1) ∨ p1)))) → (True → p5)) ∨ (p5 → p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303777685657369955221625515598 : (p1 ∨ (((p3 ∨ ((p4 → (False ∧ ((((p5 → p2) ∨ (p4 ∧ (p5 ∨ p2))) → (True ∨ ((p5 ∨ p5) → p3))) → p2))) ∧ p1)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175472652338121181042044414810 : ((p2 → ((p4 ∧ (False ∨ (False → True))) ∨ (((p1 ∧ (True ∧ p3)) ∨ p5) ∧ p5))) → (((True → ((p4 → p5) → (True ∨ True))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667369815797507240074328886053 : (((((p5 → p2) ∨ (p3 ∨ ((((p1 → p1) ∧ (p1 ∧ (((p3 → p3) → p1) → p4))) ∨ (False ∧ p1)) → p5))) ∧ ((p5 → p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113851507989038057335038685800 : (((False → ((True ∧ (((p5 ∧ (False → False)) → ((p2 → (False ∨ (True ∧ (p1 ∧ p3)))) ∨ p2)) ∨ p1)) ∧ False)) → (p5 ∧ p4)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233165619509147182347209515865 : ((p5 ∧ (False ∨ p1)) → ((((False → p1) → p2) → p2) → ((((p2 ∧ p2) ∧ (True → ((True ∨ (True → p2)) ∨ p5))) → (p3 ∧ True)) ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116992179078996252651317426851 : (((True ∨ p1) → (((p3 → (((False → (p4 ∨ ((p1 ∧ p1) → True))) → False) ∧ ((p1 ∧ (p5 → False)) ∧ p2))) ∧ p3) ∧ False)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315712712172522178595061943548 : (p3 ∨ ((p5 ∨ p2) ∨ ((p5 ∨ (False ∨ p2)) ∨ (True ∨ ((p3 ∧ (((p4 ∨ (p1 ∨ p4)) → p3) ∨ (p1 → (p1 → (p5 ∨ p4))))) ∧ p4))))) := by
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
theorem thm_5_vars_336292777548515678901066750496 : (p1 → (((False ∨ ((p5 ∨ (p3 ∧ p1)) ∨ (p5 ∧ p2))) ∨ ((False → p4) ∧ ((((False ∨ p4) ∨ True) ∨ (False → p4)) ∨ (p1 ∨ p3)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317574122196699193905989354949 : (p4 ∨ ((((((True → (p4 ∧ (((((False ∨ (p1 → p1)) → p3) → (False ∨ p3)) ∧ p3) ∧ True))) → (p3 ∧ False)) → p5) ∧ p5) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140948078692037139179992916521 : ((((p4 ∧ ((p4 ∨ p4) ∨ p3)) ∨ ((False ∨ p2) ∧ p1)) ∨ (((p3 → (((p5 ∧ True) → p3) ∧ p5)) ∨ p3) ∨ p4)) → (False ∨ (False → p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304718009362995994720194241554 : (p1 ∨ (((p2 ∧ (p1 ∨ (((False ∨ False) → ((p3 ∧ (True ∧ (True ∨ (False ∨ p4)))) → p4)) ∨ p1))) ∨ (p4 → (p5 ∨ p3))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627651369744506199214708878348 : ((((((((False ∧ ((p1 → p5) ∨ (True → (True ∨ p5)))) ∨ p2) → ((p3 → p2) → (p2 ∧ True))) ∧ ((True → p4) → p1)) ∧ p1) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648254652967084575693602346151 : (((((p4 ∨ (((True ∧ p1) ∧ p5) ∧ (((p1 → p4) → p2) → (((((p5 ∨ p1) → p3) ∨ p1) ∨ False) → False)))) ∧ False) ∧ (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156686317342649203833750107355 : ((((((p4 ∨ p4) ∨ p2) ∨ (p3 ∧ (True → (p5 ∧ (False → (p5 ∨ True)))))) → (p4 ∧ False)) ∧ True) ∨ ((True ∧ False) → ((p1 → p2) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68626783084103177899924804233 : ((p4 → ((p2 ∧ (p5 ∨ (((p1 → p2) ∧ (((False ∧ p4) ∨ (((p4 → (p3 ∧ (p4 ∧ p1))) ∧ p4) ∧ True)) ∨ p2)) ∨ p1))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147633772125465455876506119417 : ((((((p3 ∨ p3) → ((True ∧ p2) ∨ p5)) → (((p2 ∨ p1) → p4) → ((p5 → p4) ∨ p2))) → p2) → p2) ∨ (p5 → (True → (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689764130715654286451360278049 : ((((((p3 ∨ p2) ∧ p2) → (((((p4 → True) ∨ p5) → (True ∨ True)) → False) ∨ p1)) ∨ (p3 → (p3 ∧ ((True → (p4 ∨ True)) ∧ p3)))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58331498601901246955010444513 : (((False ∨ p1) ∧ (True → (p4 ∨ ((p2 → (((p5 ∨ (((p5 → (p1 ∨ True)) ∨ p1) ∧ p3)) ∨ ((p4 → p5) → p4)) ∧ p2)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51875815656985977777274547505 : ((((p1 ∨ ((False ∨ (p5 ∨ (False ∧ p1))) ∨ (p4 ∧ (p4 ∧ (False → p1))))) ∨ False) ∨ (((True ∧ (True ∧ False)) ∧ (p4 ∧ p5)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113755024858494713950076578644 : (((((p3 → (p2 → (False ∨ p5))) ∧ (p3 ∧ p2)) ∧ (((((True ∧ False) → (p2 → p3)) → p5) ∧ p2) → p3)) → (p5 ∧ p2)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327189574205123810382396214419 : (True → ((p3 ∨ (((((p5 → ((p5 ∧ p2) ∧ p2)) ∨ p4) ∨ (True → p2)) ∧ (((True → p3) ∨ p2) ∧ ((p4 → p4) ∨ False))) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684855759749141894634264004104 : (((((p5 → p5) → (p1 ∧ ((True ∧ (p1 ∨ (p1 ∧ (p3 ∧ (True ∧ False))))) ∨ (p1 → p2)))) ∨ ((p4 ∧ p4) → ((p5 ∧ False) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747460573540020953599945154091 : ((((True → False) → ((p4 ∧ p2) ∨ ((True ∧ p4) ∧ (((False → p3) ∧ (p1 ∧ (p2 ∨ (((p3 → True) ∧ (p2 → p5)) → p5)))) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259921251864211350096257201985 : ((p1 → p5) → ((True → (False ∨ (True ∧ (((False ∨ (p2 ∧ p5)) ∨ (True → (False ∧ (p5 ∧ (p1 → False))))) ∧ ((True ∧ p4) ∧ True))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4086373714428498477081488629 : (p3 ∨ ((((p3 ∨ p5) ∨ p4) ∨ (p2 ∨ (True ∨ ((p3 ∧ p2) ∧ (((p2 ∨ p5) ∨ p5) ∧ ((p2 → p4) ∨ (p2 ∨ p4))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349981629300543607345835811174 : (p4 → (((((False ∨ ((((False → p4) ∧ (((((p4 ∨ False) → p2) → (True ∨ p1)) → False) → p3)) → p1) → p2)) ∧ True) → False) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135698116386217157188127783011 : (((((True ∧ False) ∧ ((True → p4) ∧ p4)) ∧ (p2 ∨ (p1 → (True ∧ p2)))) ∧ ((p3 ∧ (True → (p1 ∧ p5))) ∧ p3)) ∨ ((False → p5) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626197179330371610206935511696 : ((((p3 → ((((p3 ∧ p5) ∧ (((p2 ∧ True) ∧ ((p3 ∨ p2) ∧ False)) ∨ (False → (p5 → (p2 ∨ p3))))) ∨ False) ∧ (False ∨ False))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64225181155363490953165254234 : ((False ∨ (p5 ∧ ((p2 ∧ (p2 → p1)) → (((False → p1) → ((True ∧ p4) ∨ p3)) ∧ ((((True → False) → (False ∨ False)) ∨ False) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683055255259111561295032599378 : ((((False ∧ ((((p4 ∧ p1) → (p5 ∧ (p2 ∧ ((False ∨ (False → p5)) → p3)))) → p4) → p1)) ∧ (p1 → ((p2 → p1) ∧ (p3 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661288641199982716180138631641 : (((((((((((False ∨ p2) ∨ (p4 → p3)) ∨ p1) ∨ (p1 ∧ True)) ∨ (p1 → (p4 ∧ p1))) ∧ p4) ∨ p4) → (p4 → p2)) → (p5 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158559544269816687473753537316 : ((True ∧ (((True ∧ (p2 ∧ True)) → ((((p5 → False) ∧ ((p3 ∧ True) ∨ p1)) ∨ p4) ∧ p1)) ∨ True)) ∨ (p3 ∧ (((True ∧ p4) ∧ p5) → True))) := by
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
theorem thm_5_vars_174336413040678751331475303382 : ((((((p4 ∧ (p1 ∧ p5)) ∧ (p2 → False)) → p1) ∨ p3) → (True ∧ (False ∧ p1))) → ((p2 ∨ p3) ∧ ((False ∧ ((p2 ∧ False) ∨ p3)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ (p1 ∧ p5)) ∧ (p2 → False)) → p1) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : ((((p4 ∧ (p1 ∧ p5)) ∧ (p2 → False)) → p1) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h13
  -- We need to get the right conjuct of h21 based on <expert-advice>.
  let h22 := h21.right
  -- We need to get the left conjuct of h22 based on <expert-advice>.
  let h23 := h22.left
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667650273069954388528582058567 : ((((p3 ∧ ((((p3 ∧ p3) → ((p5 ∧ p2) → ((p5 ∨ (False ∧ p4)) ∨ p3))) → p2) ∨ ((p5 ∨ True) ∧ p2))) ∧ ((p5 ∨ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698214635944051672857990227341 : ((((((p4 ∨ p1) ∧ (p3 → ((p5 → p3) ∧ (p3 ∧ p4)))) → p4) ∨ ((p5 → (((p3 → p5) ∨ p3) ∧ p3)) → ((p5 ∨ p5) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187648103391807662846618061623 : ((p5 ∨ (p1 ∨ ((p3 ∨ (p1 ∨ (p5 ∧ p2))) → (p4 ∨ True)))) → (((p3 → p3) ∧ ((p1 ∧ (True ∨ p3)) ∨ (p3 ∧ p3))) ∨ (p4 → True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147232134115338593929058172514 : (((((((((p4 → p4) ∧ (False → True)) ∧ p4) ∨ (p5 → p3)) ∨ ((p5 ∨ p1) ∨ p5)) ∨ p3) ∧ p5) ∨ True) ∨ (((p4 → p4) ∨ p3) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228883437971503589414881639753 : ((p4 ∨ (p1 ∧ p4)) ∨ (p3 ∨ ((((True ∧ (p4 ∨ True)) ∨ p5) → ((p1 ∧ ((((True → False) ∧ True) → (p1 ∧ True)) ∧ True)) ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313978456539433333799590503563 : (p3 ∨ ((((((False ∨ p4) ∧ p3) ∨ p5) ∧ ((p1 ∨ False) ∧ p5)) → ((p5 ∧ p2) ∨ ((p4 ∨ p3) ∨ (True ∨ (p2 → p3))))) ∨ (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325071971693398481635213339360 : (p5 ∨ ((p4 ∨ p3) → (((((p3 ∧ (p3 → False)) → (True ∨ True)) ∧ True) → p5) ∨ (((True ∧ ((False ∨ True) → (p5 ∨ p3))) ∨ True) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184850869780345433318164911448 : (((p5 → ((False → True) ∨ True)) → ((p4 ∨ (p2 ∨ p4)) ∨ p3)) ∨ ((True ∧ (True ∧ ((True ∧ (p5 ∨ p5)) ∨ (p4 ∧ True)))) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307272650658761716325321961886 : (p1 ∨ (p2 ∨ (((p3 ∧ p3) → False) → (((p1 ∨ ((p4 → p3) ∨ (((False ∧ p1) → p3) → (False → (p1 ∨ (p2 ∨ False)))))) → False) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ ((p4 → p3) ∨ (((False ∧ p1) → p3) → (False → (p1 ∨ (p2 ∨ False)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85791791407668079804410483600 : ((((((p5 ∧ False) ∧ True) → p3) ∨ (p1 ∨ (p4 ∧ (p5 ∨ p3)))) → (((True ∨ (p3 → (True ∨ ((True ∧ False) ∧ True)))) ∧ True) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∧ False) ∧ True) → p3) ∨ (p1 ∨ (p4 ∧ (p5 ∨ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183456816265834761851133945824 : ((p2 ∨ ((p5 ∨ True) ∨ ((((False ∧ p1) ∧ p1) ∧ True) ∨ p2))) ∧ ((p4 ∧ ((p2 ∨ p3) ∧ (p2 → (p1 ∨ (p5 → (p5 → p1)))))) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200303997449771530100262149330 : (((p2 ∧ p1) ∧ ((p2 ∨ (p4 ∨ p4)) → p2)) → ((((p4 → ((False ∨ p2) ∧ p3)) ∨ True) ∨ p4) → (p5 ∨ (((p5 ∨ False) ∧ p1) ∨ True)))) := by
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
      let h5 := h1.left
      let h6 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687738358839020241234879288675 : ((((((((((p4 ∧ p5) ∧ p4) ∨ p4) ∧ p5) ∧ (p2 ∧ p1)) ∨ p1) ∨ (p4 ∧ p5)) ∧ (p5 ∨ (p5 ∨ ((False ∧ (False ∨ p4)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228417166944920884762829407032 : ((False ∨ (p2 ∧ p5)) ∨ ((p5 → (True → (((p4 → (False → (p2 ∨ False))) → (p1 ∧ (p3 → p2))) ∧ p2))) ∨ (p4 → (p4 ∧ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46475096110502962135024002099 : ((((p3 ∨ (p2 ∧ p4)) ∧ ((((((False ∨ p2) ∧ p5) → ((p5 ∨ p1) ∧ p1)) ∨ p1) ∨ (False ∨ p3)) ∧ (p1 ∨ p4))) ∧ (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174231432473236661499924013045 : ((((p4 ∨ p5) ∨ (False ∨ (p2 ∨ (p5 ∨ (p4 → (p3 ∨ p1)))))) → (p1 ∧ False)) → ((p2 → (False → p4)) ∧ (p3 → (p1 → (p2 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ p5) ∨ (False ∨ (p2 ∨ (p5 ∨ (p4 → (p3 ∨ p1)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134781783171067722076263498088 : (((p1 ∧ (((((True ∧ True) ∨ (p3 → p4)) → p3) ∨ ((p5 → ((True ∨ False) ∧ p2)) → (p2 ∨ p4))) → p4)) → p5) ∨ ((p4 ∧ p1) → p4)) := by
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
theorem thm_5_vars_759160214868563906734064755460 : (((p2 ∧ (((p5 ∧ (((True ∨ ((True ∧ (p3 → False)) → False)) → (p5 → (True ∧ (p1 → (True ∧ p2))))) ∨ p2)) ∧ False) ∨ (p3 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382996842697581255387002816148 : (((((p2 ∧ ((True ∧ True) ∧ (p1 ∧ ((((False ∨ p5) → (p1 ∨ p5)) ∧ (p1 → ((p1 ∧ False) → (False ∨ False)))) → p1)))) ∨ p2) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_726117167382685363134717619934 : (((((p2 ∧ p3) ∨ False) ∨ (p2 ∨ (((p1 → (((False → (p1 ∧ True)) ∧ True) ∨ (p3 ∧ False))) ∨ (p5 ∧ (p5 ∧ p2))) → (p1 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327817464699408219526297568508 : (True → ((((False ∨ True) → ((p4 → ((p1 ∧ (((p4 ∨ p4) ∧ p2) → (p3 → (p5 ∨ (False ∨ p3))))) ∧ p5)) ∧ p3)) → p3) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60056208607253778126870388943 : (((p2 ∨ False) → ((True ∨ (True → p5)) → ((p1 ∨ (p1 ∧ (((p4 ∧ ((p2 → p1) ∨ ((p3 ∧ p3) ∨ False))) ∧ p4) ∨ p5))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215398506436802039225856460834 : ((p2 ∧ (p2 ∨ (False ∨ p3))) ∨ (((True → (p2 ∧ (True ∧ (p1 ∨ p1)))) ∨ True) ∨ (((((False ∧ False) ∧ p4) → (False ∨ p4)) ∧ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134070933783113637275980743496 : (((((((p2 ∨ True) → p1) → ((True ∧ p1) ∧ ((p5 → True) → (p4 → (p3 → (False ∨ p5)))))) → False) → p3) ∨ p5) ∨ ((False ∧ True) → p4)) := by
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
theorem thm_5_vars_715524193857607573728509057572 : ((((((p4 → True) → p5) ∧ p4) ∧ (((p2 ∧ ((p2 ∧ p4) → (False → True))) ∧ (((p5 → True) → False) → True)) ∨ ((p1 ∧ p2) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184805383527572043062052574794 : (((p4 ∨ (p2 ∨ (p3 ∨ p4))) ∨ (p4 ∧ (p4 ∨ (p1 ∧ True)))) ∨ (((p5 ∧ (p3 ∧ (p5 ∧ (True ∧ p1)))) → p3) ∨ (False ∧ (p3 → p4)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648562008565366208042052807799 : (((((((p5 ∧ ((p3 ∨ True) ∨ (p4 → (p4 ∧ (p3 ∨ p1))))) ∨ p4) ∨ ((p2 → p3) ∧ ((p5 → True) ∨ p2))) ∨ p5) ∧ (False → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147554291295929039959658718000 : (((p5 → (p2 ∨ ((((p4 → (False ∨ p1)) ∨ (True ∨ (p4 ∧ p5))) → (p5 ∧ (p4 ∨ p1))) → p2))) ∨ p2) ∨ (p3 → ((p2 → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356166327390082279287260920747 : (p5 → ((p2 ∧ ((p2 → ((p1 ∧ ((p5 ∨ ((p2 ∨ p1) ∧ p5)) ∧ (False → p3))) ∧ p2)) → p4)) ∨ (p2 → (((p2 → p5) ∧ False) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190123250367792130559752545657 : (((((p5 ∧ p4) ∧ True) → (True ∧ (p2 ∨ False))) ∧ p4) ∨ ((((p4 ∨ p1) ∨ (p5 → p5)) ∨ (False ∧ (True ∨ (False ∧ True)))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138142124558536540111079891421 : ((p1 → (((p5 → (p4 → (p4 → ((p4 ∨ p2) ∨ True)))) → ((p4 → (((p5 ∧ p3) ∧ True) ∧ p4)) ∨ p5)) ∧ True)) ∨ (True ∨ (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264551098674369823087266493971 : (True ∧ (((p5 ∨ p4) ∨ p2) ∨ ((True → p2) ∨ ((p5 ∨ False) → (((p3 → p2) → (((p2 → p3) ∨ p4) → False)) → (p2 ∨ (False ∨ True))))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299370677703694960443900121290 : (False ∨ (((False ∨ p4) ∨ ((((True ∧ p1) → ((p2 ∧ p5) ∧ ((p5 ∨ True) → (False ∧ p1)))) ∨ ((p4 ∧ (p1 ∧ p4)) → p1)) ∨ p2)) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300590749388604141481776615161 : (False ∨ (((p5 → (False ∨ ((p3 ∧ (((p3 → p3) ∨ ((p2 ∨ (True → p4)) ∧ p4)) → True)) ∧ p4))) → p4) → (p5 ∨ ((False ∨ p4) ∨ True)))) := by
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
theorem thm_5_vars_115419358929828491547112441905 : (((((p3 → p4) ∧ (p2 → (p1 ∧ p4))) ∧ False) ∨ (((p1 → (((p5 ∨ p1) ∧ p5) ∧ p3)) ∨ p1) ∨ (p5 ∧ (False ∨ p1)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63219657522845608478903741973 : ((p5 ∧ (((True ∧ False) ∧ (True → ((((p1 ∧ p3) ∧ p3) → (p1 ∧ p5)) ∧ (p1 ∨ p1)))) ∨ (((p2 → p2) ∨ p5) ∨ (p4 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42641671518355644105146719835 : (((p3 ∨ (p3 → ((((p2 ∨ p3) ∨ ((p2 ∧ (False → (False ∨ False))) ∧ (p2 ∧ p5))) → ((p1 ∧ p4) ∧ (False ∨ p1))) ∨ p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742484397089326982759211643254 : ((((p2 → False) ∨ (((True → False) → (p1 ∨ (((((True ∨ p5) ∧ True) ∧ p5) ∨ p3) ∧ (((p4 ∨ p2) ∧ p2) ∨ (p1 ∧ p4))))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247551621982205345955322466264 : ((False ∨ p4) ∨ ((((False → p4) → (False ∧ ((p2 ∨ p1) ∨ (True → p1)))) ∨ p1) → (((p2 ∧ p3) ∨ True) ∨ ((p1 ∨ (p4 ∧ True)) ∨ p4)))) := by
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
theorem thm_5_vars_341676377799687233876115434803 : (p2 → (((p3 ∧ ((((((p5 ∧ ((p5 ∧ p5) ∨ (p3 ∨ (p3 → p1)))) → p5) ∨ True) → (True → False)) ∨ p4) ∨ p2)) ∨ p1) ∨ (p2 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51998261849208688907802551762 : (((True ∧ (p1 → ((((p2 → ((p4 → (True → p2)) → p4)) ∧ True) ∨ False) ∧ p2))) ∨ (((p5 → p2) ∧ p2) ∨ ((p3 ∨ False) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18931117442115812783907579746 : (((p5 ∧ (((p4 → (p4 ∧ (p2 → (True → ((p1 → p4) ∧ p1))))) ∧ (p1 ∧ p2)) ∨ p2)) ∨ (p4 ∨ ((p5 ∧ (p4 ∧ p1)) → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308390278544965826527323396790 : (p2 ∨ (((((p5 ∨ p3) → p1) ∧ ((False ∧ (p4 ∨ (p2 ∨ ((((p5 ∨ p4) ∧ (p4 ∧ p4)) → (p3 ∧ True)) → False)))) ∧ p4)) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301517998647181578042122668471 : (False ∨ (((False ∧ p2) ∧ p1) ∨ (p2 ∨ (True ∨ (((False ∨ p2) ∧ p4) ∨ ((p4 → (p1 ∧ p1)) ∧ ((p2 ∨ (p3 → False)) ∧ (False ∧ p4)))))))) := by
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
theorem thm_5_vars_761153055506455753710931664890 : (((p2 ∧ (p4 → ((((((True ∨ (True ∨ p4)) ∨ p5) ∧ True) ∧ ((p3 ∨ False) ∧ p1)) ∨ ((p2 → ((p3 ∧ p5) ∨ p4)) ∧ p5)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115941920402401327835854602936 : (((p1 ∨ ((True → p1) ∧ p1)) ∨ (((((p2 → True) ∧ (p1 ∧ (p2 → ((False ∨ False) → p1)))) → True) → p3) ∨ (True ∨ p2))) ∨ (p3 ∨ p5)) := by
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
theorem thm_5_vars_217320061298020425363591446471 : (((True ∨ (p2 → p2)) ∨ p5) → (((p4 → p1) ∨ p5) → ((True → p2) ∨ (((False → p4) ∨ (p2 ∧ (p5 ∨ (p4 → (False ∧ p1))))) ∨ p3)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192476263924362952562058540444 : ((((p3 ∨ ((p1 ∧ p1) → p5)) → (p5 ∧ p2)) ∨ p5) → (((p5 ∧ (False ∨ (p4 → (p3 ∧ (p2 → p2))))) → p5) ∨ (p3 → (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327200336940417562675517068377 : (True → ((p5 ∨ (((p4 → (True ∧ ((p1 ∨ p3) ∨ p3))) → (False ∨ (((p1 ∨ p1) → p2) → (p5 ∧ (p2 ∧ (p4 ∨ p4)))))) ∨ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319626406417650791512763540930 : (p4 ∨ ((((p1 ∨ (p5 ∧ (p3 → p5))) ∧ p4) ∧ p4) ∨ (False → (((p3 ∧ ((p1 ∧ p5) → p4)) ∨ ((p1 → p4) → (p2 ∨ p4))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44909392777512321652713904441 : ((((False → (p1 ∨ p4)) → (((p2 ∧ ((True ∧ (((p4 ∧ True) ∨ (True → p4)) ∨ p3)) → p5)) ∨ p4) ∧ ((p4 ∧ p2) ∨ p4))) → p4) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p1 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339666112025973156423992639479 : (p1 → (p3 ∨ ((p3 ∧ ((p3 ∧ ((((False ∧ False) → (p2 → p1)) → (((p5 → p1) ∧ (p3 ∨ (p4 ∨ p1))) ∧ p2)) ∨ p4)) ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41627852879121216972549276174 : (((((p3 → (False ∨ False)) ∧ ((True → False) → p3)) → ((p5 ∨ ((((True ∨ (True ∧ True)) ∧ p4) ∨ False) ∨ (p1 → p4))) ∨ True)) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_356164967634974510155814681446 : (p5 → ((True ∧ ((False ∧ p3) ∨ (p2 ∨ (((True ∧ ((False ∧ p4) ∧ True)) ∧ (False → p3)) ∧ True)))) ∨ ((True ∧ p5) ∨ ((p1 ∨ False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158378035537024237178044832633 : (((True → False) ∧ (p3 → ((p1 ∧ (((True ∧ p5) ∧ p3) → p5)) ∨ (p4 ∨ (p1 ∧ (p4 ∨ True)))))) ∨ ((p1 ∧ p5) → ((p1 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_260743455751519223707438863441 : ((p3 → p4) → ((p1 → False) → ((p5 ∧ ((p4 ∧ p2) → (False ∨ False))) ∨ ((p2 ∧ ((p3 ∨ ((False → p1) → p2)) → (p4 ∧ False))) → p1)))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ ((False → p1) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253968714867129807791525875148 : ((p1 ∧ p5) → ((False ∧ ((((False ∨ (((False → (p2 → True)) → False) ∧ (p2 ∨ (p4 → p5)))) → (p1 ∧ p4)) ∨ (p5 ∧ p4)) ∨ p4)) ∨ True)) := by
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
theorem thm_5_vars_656137590576105919480064109986 : (((((p5 ∨ (False ∨ (p2 ∧ (((True ∨ ((True → p5) ∧ p1)) ∨ p4) → p4)))) ∧ (p5 ∧ ((p5 → (False ∨ p1)) ∧ False))) ∨ (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_475908679137845876213069042103 : (((((p2 ∧ (((p1 → p1) → (True → p1)) → p4)) ∨ p3) ∨ (p5 → (((p5 ∨ True) ∧ ((p2 → (p5 ∧ True)) → p2)) ∨ (p2 → True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180502393635761166686638940931 : ((((p5 → p2) → (p5 ∧ ((p1 ∧ p3) ∧ p5))) ∧ ((p2 → True) ∧ p5)) → (p2 → ((True → (((p3 → (p3 ∨ True)) → p5) ∧ p2)) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115396421834611856417881641309 : (((p2 ∧ (((p1 ∧ False) ∨ (p3 ∨ True)) ∨ p1)) ∧ (((p4 → (((p4 → p4) → p4) ∧ p5)) → p1) → ((p3 ∨ p3) ∨ False))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



