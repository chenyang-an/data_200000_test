variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256516081092675263044467003189 : ((False ∨ p5) → (((((p3 ∧ p4) ∨ True) → (((p1 ∧ (p4 ∨ True)) ∨ (p2 ∧ (p5 → ((p1 ∨ p5) ∧ (p5 → p2))))) → p1)) ∨ False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316446272934788315498086846762 : (p3 ∨ (p1 ∨ (((p2 → ((p4 ∧ ((p2 ∧ (p3 → ((p3 ∨ p4) → p5))) ∨ p2)) → p2)) → p5) ∨ (True ∨ (p5 ∨ (True ∧ (p5 ∨ p4))))))) := by
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
theorem thm_5_vars_312335733126898758924515677816 : (p2 ∨ (p2 → (p4 ∨ ((((((((False ∧ False) ∧ p2) ∨ True) → False) ∧ p2) → (False ∨ ((p3 ∧ (False → p1)) → (p5 ∨ p1)))) ∧ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((False ∧ False) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762543097253608108337037656 : (((p2 ∧ p3) ∧ (p3 ∧ (p5 ∨ (p3 ∨ ((((p4 ∨ (False ∧ ((p2 ∧ (p2 ∨ False)) ∧ False))) ∨ False) → True) → (p2 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148205137974254062094767702520 : (((p5 ∧ (((((False → (True ∧ ((p4 ∧ False) ∧ False))) → p1) ∧ p4) ∨ True) ∨ p4)) ∧ ((p3 → p4) → p3)) ∨ (p5 → (p2 → (p5 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779493248676755652642761537540 : (((p2 ∨ (((((((p1 ∨ False) ∨ p4) ∧ p4) ∧ (p4 → False)) ∧ p4) ∨ (True ∨ (((p5 → (p3 ∧ False)) ∧ p4) → (p3 ∨ p4)))) ∨ False)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197992278001263483031317223956 : (((p5 ∨ True) ∧ (((p2 ∧ p4) ∨ p3) ∧ p1)) ∨ ((((p3 ∨ (p1 ∧ p1)) → ((p2 ∨ (p4 ∨ ((True ∨ True) ∨ p3))) ∧ p1)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56002548312171846614708572296 : (((((p3 ∧ p1) ∧ p4) ∨ p5) ∨ (p3 ∧ ((p3 ∨ ((p3 ∨ (True ∨ (((False ∧ p2) ∧ p3) ∧ p4))) → (p5 ∧ p2))) ∨ (p4 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113294778662103917616968409882 : (((((p2 → p1) → ((True → (p2 ∧ False)) ∨ p3)) ∨ (((p3 ∨ True) ∧ False) → ((p4 ∨ p1) → (p3 ∧ False)))) ∧ (False ∨ p4)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317364135823260852513640081671 : (p4 ∨ (((((p1 → ((False ∧ (p2 ∧ False)) ∧ p4)) ∨ p1) ∨ True) ∨ (((p3 ∨ p2) → (p2 ∨ False)) ∨ (p3 → ((True ∧ True) → p1)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_47148147660538103037245280954 : ((((((p4 ∧ p5) ∨ p3) ∧ ((((True ∨ True) ∧ (p4 ∧ p5)) → (True → True)) ∧ p1)) ∨ (p1 ∨ (True ∧ (p4 ∨ p3)))) ∨ (True ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192962306047738931214356785687 : (((p5 ∧ ((p4 → p5) ∧ (True → p4))) ∨ (False ∨ True)) → ((p1 ∧ p4) ∨ (False ∨ (False → (p2 ∨ (((p3 ∧ (p2 → p4)) ∨ p1) ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183940767814982477571108549203 : (((p1 ∨ ((((p2 → p1) ∧ p4) ∧ p2) ∧ (p3 ∧ p1))) ∧ p1) ∨ (p3 ∨ ((False → False) ∨ (False ∧ ((False ∨ p3) → (p2 ∧ (p4 ∨ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147052767193138868336706650649 : ((((((p1 ∧ (p1 ∨ (p2 → p4))) ∨ (p2 ∧ True)) ∧ p4) ∨ ((((True ∨ p4) → p3) ∨ p4) ∨ p1)) ∧ p3) ∨ (p2 → (False → (False ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621109077198432655210817355588 : (((((p4 → True) → (((p2 ∨ p4) ∧ (((p5 → (((p1 ∨ (p2 → p4)) → p1) ∧ False)) → False) ∧ (p4 → True))) ∨ (p4 → p1))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_46891371846056650932217939440 : (((((p5 → (((((p4 ∨ (p1 ∧ p1)) → (True → p4)) ∨ ((False → (p4 ∨ True)) → p1)) → p1) ∧ p2)) ∨ p1) ∨ True) ∨ (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48953811569639911013696631077 : ((((p3 ∨ ((((((p2 → p2) → p2) ∧ p1) → (False ∨ p4)) → p4) ∨ ((p4 ∨ (p4 ∧ p4)) ∧ p4))) ∧ False) ∨ (p5 ∧ (False ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135875497154803422992002185757 : ((((p3 ∧ True) ∧ (p2 ∨ (p4 ∨ (p3 → (p2 → (p3 ∨ True)))))) ∨ ((p5 ∧ ((p3 ∧ p1) ∧ True)) ∧ (p2 → p3))) ∨ ((False ∧ p3) → p3)) := by
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
theorem thm_5_vars_218851591863852534815964413443 : ((p2 ∧ ((p1 → p4) → False)) → (((((p3 ∧ p5) ∨ (True ∧ p5)) ∨ False) ∨ (p3 → (p4 → ((True ∨ p3) ∧ (False → p4))))) ∧ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134945577113504483170892753907 : (((((True ∧ p3) ∨ (p1 ∨ (p5 ∨ ((p4 → (p5 ∨ True)) ∧ ((p4 → False) ∨ p4))))) → (p3 ∨ p5)) ∧ (p5 ∧ True)) ∨ ((True ∨ p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776084420434043333594870494165 : (((False ∨ (p5 → ((((((False → (p2 ∨ (True ∨ True))) ∧ p2) ∨ p5) ∨ False) ∧ p4) ∨ (((p4 ∧ (p2 → False)) → (True ∨ p2)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744300383827238557615113490498 : ((((p1 ∧ p4) → ((p2 → ((True → (((False ∨ p1) ∨ (p1 → p2)) ∧ p5)) → ((p3 ∧ p3) ∨ (p5 ∧ False)))) ∨ (p5 → (True ∨ p4)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315510545690827118344914530557 : (p3 ∨ ((False → (p3 → p1)) → (((p5 ∧ ((p5 → False) → p2)) ∧ True) → (((p2 ∧ (p5 ∧ (p4 ∧ (p1 → p3)))) ∨ p5) ∨ (p2 → p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231153120416133584421447372314 : (((p2 ∨ True) ∨ p2) → (((((((p1 ∧ p5) ∨ (p2 → p1)) ∧ p4) ∧ (((p2 → p1) → p1) → p2)) ∨ (True → p5)) ∧ False) ∨ (True ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738729987927381738260863097347 : ((((p2 ∧ p2) ∨ (p3 ∨ ((((p2 ∧ ((p1 ∨ p1) ∨ p2)) ∧ ((True ∨ (p5 ∧ ((p2 ∨ p2) ∨ True))) ∧ True)) ∨ p5) ∨ (p3 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111681559330249710230957590300 : ((((((p1 ∧ p3) ∨ ((False ∨ (False → (True ∨ p3))) ∨ ((p5 ∧ (p3 ∧ ((p5 ∧ True) ∧ p2))) ∨ p4))) ∧ p3) → p4) ∨ p3) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56728860340271767201859009607 : ((((p2 ∨ p5) ∨ p3) ∧ (((p2 → ((p3 → ((p5 ∧ ((p3 → True) ∨ p1)) ∨ (p3 → p4))) ∧ (p1 ∧ False))) → (p1 ∨ p2)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731962894362864200233432414319 : ((((p5 → (p5 → p2)) → (((p2 ∧ p4) ∧ ((((p5 ∨ True) ∧ True) ∧ (False ∨ ((p1 ∧ True) ∨ (p1 → p3)))) ∨ p3)) ∧ (p4 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178558480066607244810234343575 : (((((p5 ∨ p5) → (p4 ∧ p5)) → p2) ∧ ((p5 ∧ (p1 → p4)) ∧ p3)) ∨ (((p4 ∨ True) ∨ (p3 ∧ p5)) ∨ ((p4 ∨ (p1 ∧ p4)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345422587961753053282051925604 : (p3 → (((True ∨ ((((p4 → p3) ∧ (p3 ∨ (True ∧ p1))) ∨ False) ∧ ((p1 ∨ p4) → ((p1 → p4) → (False ∧ (p1 ∧ p3)))))) → False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741457049775674846379054295958 : ((((p5 ∨ p2) ∨ (((p5 → (p4 ∧ p5)) → ((p2 ∧ True) ∨ (p2 → ((p5 ∨ p3) ∨ ((p3 ∧ (True ∧ (p1 ∧ p4))) → p4))))) ∨ p5)) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50309092823624227317301834117 : (((((((((p5 ∧ p1) ∧ p2) ∧ (True ∧ True)) ∧ p1) ∧ p1) ∧ False) ∨ (True ∧ (p1 ∧ (p2 ∧ False)))) ∨ (((True → p2) ∨ True) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112035465946818419257687413254 : ((((p5 ∧ (p5 ∨ False)) ∨ (p3 ∨ (p1 ∨ (((True → ((p5 → p2) ∨ (True ∧ (p3 → p5)))) → (False → False)) ∧ False)))) ∨ p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135460110493578373603842377368 : (((((p4 → False) → (((((p2 ∨ p2) ∧ p2) → (p5 → p5)) → (p4 ∨ p5)) ∨ True)) → p2) → ((True ∧ False) ∧ p1)) ∨ (p4 → (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668711640728353026785009870862 : (((((((p3 → ((p3 ∧ False) ∨ ((p5 ∧ p5) → (False → ((p5 → (p1 ∧ p3)) ∨ p5))))) ∧ p4) ∨ p5) ∨ p4) ∨ (True ∧ (False ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596289433664691902533189771021 : (((((p2 → (p1 → ((True ∧ (p4 ∧ p2)) ∨ False))) ∧ ((p2 → (p3 ∨ (False → True))) → (((True ∨ p5) → (p4 → p2)) → p4))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265828015849399838260592793710 : (True ∧ (p5 ∨ (((((p5 ∨ (False ∧ (p4 ∨ ((p4 ∨ p3) → p3)))) ∨ p5) → p5) → (((False → True) → p5) → (p3 ∨ p5))) ∨ (p3 ∧ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691217177914642302191092957461 : ((((((p1 ∧ p2) → ((True ∨ False) ∨ p1)) → (((p3 ∨ False) → p5) ∨ (True ∧ p1))) → ((p1 → (p1 → p5)) ∧ (p5 ∧ (False ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391121420525096523304161780934 : ((((((p1 ∧ (p1 → (True ∧ p3))) ∨ p3) ∨ (((((p2 ∧ False) ∨ (p5 ∧ (p3 ∨ p1))) → ((p1 → p2) → p1)) → p3) ∧ p1)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_142970665478236489002604304281 : ((True → (((p1 → p3) → (((False ∨ True) → (p2 ∨ (p4 → (False ∧ True)))) → (False ∧ (p1 ∧ (p1 ∨ p5))))) ∧ p2)) → ((p3 ∧ p1) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50618126207042239481158430376 : (((((p4 ∧ (((p4 ∧ (p5 → (p4 → p3))) ∧ p1) → False)) ∨ (p1 ∧ p5)) ∧ (False → (p5 ∧ p1))) → (((True ∧ False) ∧ p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47530065933241135647957254211 : (((p4 ∨ ((p3 ∧ ((((True ∧ p1) ∨ p2) → (True ∨ (True → (((p2 → (p4 → p1)) → p1) ∧ True)))) ∧ p1)) → False)) ∨ (True ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205491276346721086454050415888 : (((p1 ∧ p3) ∧ ((False → True) ∧ p4)) ∨ (((True ∨ (((p3 ∧ True) → p3) ∧ (p5 → p5))) → p2) → (p5 ∨ (p1 ∨ (p2 ∧ (p2 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((p3 ∧ True) → p3) ∧ (p5 → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64401534589070093284371791014 : ((p1 ∨ ((((p1 ∨ (True ∨ (((True ∨ (p3 ∧ (p5 ∨ False))) ∧ (p5 ∨ True)) ∨ p2))) ∨ True) → ((p2 ∧ (p5 ∧ p3)) ∧ False)) → p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (True ∨ (((True ∨ (p3 ∧ (p5 ∨ False))) ∧ (p5 ∨ True)) ∨ p2))) ∨ True) := by
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
theorem thm_5_vars_171851405987251480839874109990 : ((((p1 → False) ∨ ((p4 ∨ ((p4 ∨ p5) ∧ (p1 ∧ (p1 → p1)))) ∧ p3)) → p5) ∨ ((True ∨ (False ∨ (p5 ∧ (p1 ∧ (p4 → True))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112134084387703286776125159419 : (((False ∧ ((((p1 → p3) ∧ p2) → (False → (p5 ∧ (p4 → p2)))) → (p3 ∧ (((p4 → p2) ∧ (False ∧ p2)) ∧ True)))) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53294891565933572384725177807 : (((p1 ∨ ((p2 → p1) ∨ (((p5 ∧ p4) ∨ (True → p1)) → p1))) ∨ (p4 ∧ ((p5 ∧ p3) ∧ (False → (False ∨ (p1 ∧ (p4 ∨ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626482057882856832242851911730 : ((((p4 → (((p5 → (False ∨ (((p2 ∨ (p2 ∨ p1)) ∧ (p1 ∧ p5)) ∧ p5))) ∨ ((p3 ∧ (True ∨ True)) ∧ True)) ∨ (p3 ∨ True))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_586140339051617721132725121585 : ((((((False ∧ (((True ∨ (p3 ∨ (p1 ∧ True))) ∧ ((p5 ∨ p3) ∨ p1)) ∨ p2)) ∧ ((p1 → (True ∧ True)) → (p1 ∧ True))) ∧ p2) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179833065233333562106452980087 : (((p5 ∧ ((p4 → (p2 ∧ (((p5 ∨ False) ∨ p2) ∧ p5))) → p3)) ∧ p3) → (p4 → (p2 ∨ ((p5 → True) → (True ∧ (False ∨ (p2 ∨ True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
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
theorem thm_5_vars_613989980088135925007830989606 : ((((((p5 ∨ (p1 ∧ ((True → p1) → True))) ∨ (p1 ∨ ((p5 ∧ p1) ∨ ((p4 → p5) ∨ (p3 → p2))))) ∨ ((p3 ∧ p2) → True)) ∨ p1) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40343187123778437965747308187 : (((((p4 ∧ ((((p1 → (p5 ∧ (True ∨ p3))) ∨ True) ∧ ((p4 ∧ p4) → ((p3 ∧ (p1 → True)) → p3))) → p1)) ∨ True) ∨ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738754533386056003333879311509 : ((((p2 ∧ p3) ∨ ((p5 ∧ (p5 → ((p2 ∧ False) → (p4 ∨ (p2 ∧ p3))))) ∧ (((False ∧ True) ∧ False) ∧ ((p3 → (True → p4)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752883841702004402951424655680 : (((False ∧ ((((True → (p4 ∧ ((p4 ∧ (True ∨ ((True ∨ (p5 ∨ (p3 → p5))) ∨ p4))) ∧ (p4 ∧ p3)))) ∧ (False → p5)) ∨ False) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749159734084948505004862166263 : ((((p5 → p1) → (p1 ∨ ((((p1 ∧ p4) ∨ ((p5 ∨ (p5 ∨ p5)) ∧ p3)) → (p2 ∨ ((False ∧ ((p2 ∧ p1) ∨ False)) ∨ True))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714570645178148244093608179921 : (((((p4 ∧ p2) ∨ (p1 → (False → True))) → ((((p4 ∨ p5) ∧ p4) ∨ (p2 ∧ (((((False ∨ p4) ∨ False) → False) ∧ True) ∧ True))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5628910267102482840594388771 : (((((False → ((False ∧ True) ∨ (p2 ∨ (p5 ∨ p2)))) → (p5 ∧ ((p4 ∧ False) ∨ (p3 ∨ (False → (p4 → p2)))))) ∨ (False → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262464809610702436528580341139 : (True ∧ ((p2 ∨ (p2 ∨ ((((True ∧ ((True ∨ (((True ∨ p3) → (p3 → p5)) ∧ p2)) ∧ (p1 ∧ p3))) ∨ False) ∧ p2) ∧ (True → p1)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200006720084882348866660410602 : ((((p5 ∨ (p4 → p1)) → p3) → (p5 → p3)) → (((p4 ∨ (p1 → (p5 ∨ False))) ∨ (True → (False ∧ True))) ∨ (True ∨ (p3 ∧ (p2 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110897955399960036629555149846 : (((((p2 → (True ∨ p2)) ∨ ((True → p1) ∧ (((p1 ∧ ((p5 → (True ∨ True)) ∨ (p1 ∧ p4))) ∨ p3) → p1))) → p2) ∧ p1) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158590932734952533491880154567 : ((True ∧ (p5 → ((True → p2) ∧ (p2 ∧ ((p4 ∨ (((p3 → p3) ∧ (p3 ∨ p5)) → False)) ∨ p5))))) ∨ (p5 ∨ ((False → (p3 ∧ p5)) ∨ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595404854302403628632083121922 : (((((p5 → ((((p3 → p1) ∧ p4) ∧ p5) ∨ (p2 → (p4 ∨ p3)))) ∧ ((p2 ∧ ((True ∨ p1) ∨ (p5 ∨ p4))) ∧ (p1 ∨ p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248794631952134530233841734498 : ((p3 ∨ p3) ∨ (p3 → ((((p5 → p2) ∧ (((p3 → (p1 → (p1 → False))) ∨ (False ∧ False)) → p5)) ∧ ((True ∧ (p3 ∨ p2)) ∨ p1)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67441267611803111233369913541 : ((p1 → (((((False ∨ ((p4 ∧ (p1 → (p3 ∧ False))) ∨ (p5 ∧ p3))) → p5) ∧ (p2 → True)) → (p4 ∧ p5)) ∨ ((p1 → p3) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186670819693300556140369459962 : ((((p1 ∧ p1) ∨ (p2 ∧ (p1 ∨ p5))) ∧ (True → (p2 ∨ p2))) → (((p4 ∨ (p2 ∧ p5)) → (p1 ∧ ((True ∨ (p2 ∧ p3)) ∧ p4))) → p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : (p4 ∨ (p2 ∧ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149662042146169626306950743761 : ((p4 ∧ (p4 ∧ ((p4 → p3) → (((True ∧ (True → ((p1 ∧ False) → (p1 ∧ True)))) ∨ (p5 ∧ p3)) → p1)))) ∨ ((p1 ∨ p4) → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42024867149082097151437134324 : ((((p1 ∧ False) ∨ (p3 ∨ (p1 → ((True ∧ (True ∧ ((((True ∨ p1) ∨ (p2 ∨ p4)) → p2) ∧ p3))) ∧ ((p5 → p3) ∨ p4))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42826502827017702825690305106 : (((p1 → ((p5 ∨ False) ∧ (p4 ∧ (((((p5 → p1) ∨ p3) → (True → p1)) → p5) ∨ ((p2 → (p3 → (p5 ∧ p4))) → p4))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258685818655310051623203598688 : ((p5 ∨ p5) → (False ∨ ((((p4 ∨ (p1 ∨ p3)) ∧ (True → (p3 ∨ (False ∨ p5)))) → p4) → (((p3 ∨ p3) ∨ p5) → (False ∨ (p3 → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191362429285379384966625248053 : (((p5 ∨ False) ∨ (((False ∨ p2) ∧ p2) ∨ (p3 → False))) ∨ (p3 → (((p3 → ((p4 → p4) → ((False ∨ False) ∧ (False ∨ p1)))) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198190854179588336236023220603 : (((False → p3) → ((p5 ∧ p4) ∧ (p5 ∧ p2))) ∨ (((False ∨ (p2 → p1)) ∧ p3) → ((p5 ∧ ((p1 ∨ (p2 → (p3 ∨ False))) ∧ False)) → p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2953087958076407112336585362 : (((False → p4) → p2) ∨ (p4 → (((p3 → (False ∧ p1)) ∨ p1) ∨ (((p2 ∨ p5) → False) → (((True ∨ p5) ∨ p4) ∧ (p2 → p4)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135868135579568610096460378504 : (((((True → p5) ∧ (True ∧ (p3 → p3))) ∧ ((p1 ∧ p2) ∨ False)) ∨ ((p1 ∨ ((p1 ∧ p1) ∧ (p3 → p4))) → p2)) ∨ ((p3 ∧ False) → False)) := by
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
theorem thm_5_vars_156873998642241325188669476183 : ((((False ∨ ((p5 ∨ False) → ((p4 → p5) → (p2 ∨ (p4 ∨ (p5 ∧ (p3 ∨ False))))))) ∧ p5) ∨ p4) ∨ (p1 ∨ (p2 ∨ (False → (True ∨ p2))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354930519892734294716445847426 : (p5 → ((p3 ∨ ((False ∨ p4) → (((p1 ∨ (((p1 ∨ False) ∧ p5) ∨ p1)) → ((p1 ∨ ((p3 → (False ∧ p5)) ∧ True)) → False)) ∨ False))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629648163932131758683022069792 : ((((((p5 ∧ ((p1 ∧ (False ∧ (((p3 ∨ False) → (((p1 ∨ p4) ∨ p5) → p5)) ∧ p5))) ∨ p4)) → ((False ∨ False) ∨ p1)) ∨ p1) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41722990000837992904594883022 : (((((p1 → (p3 ∨ p1)) ∨ p2) ∧ ((p5 ∧ ((p4 ∧ (p1 ∨ p4)) ∨ ((False ∨ True) ∧ False))) ∨ ((p3 ∨ (p2 → False)) ∧ p2))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319158503741097749612519933971 : (p4 ∨ (((((p4 → ((((True ∨ False) ∧ True) ∧ (p5 → p2)) → p1)) → p5) ∨ (p5 ∧ p5)) ∨ False) ∨ ((p2 ∧ p1) → ((p3 → p3) ∧ p1)))) := by
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
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110697086735934137674086791411 : ((((((p4 ∧ (p4 ∨ ((p2 ∨ ((False ∧ True) → (p4 → ((p3 ∧ p1) → (p5 ∨ p5))))) ∨ p1))) ∨ p5) ∧ True) ∧ p1) ∧ p3) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142497457177341042216186381810 : ((p5 ∧ (True → ((((p3 ∧ p5) ∨ ((((p2 ∨ p3) ∧ (p1 ∨ p2)) → True) → p3)) ∨ p3) ∧ (False ∧ (False → False))))) → (False ∧ (p1 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55583431403660692169821539524 : (((p2 ∨ ((False → p5) ∧ (p3 → True))) → (True → (((True ∧ ((p3 ∨ ((((p2 → True) → True) ∨ p3) → p2)) → True)) → p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724492029457209674033020437062 : ((((False ∨ (p1 ∧ p5)) ∧ (((True ∧ ((p1 ∧ (((p2 ∨ p3) ∧ p4) ∨ p3)) ∧ (p3 ∨ p2))) ∨ ((p5 ∨ p1) ∨ True)) ∨ (p5 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54501701831469584517918529011 : (((((p3 ∨ p2) ∧ p5) ∨ (p2 ∧ (p5 ∧ p2))) ∨ (True ∧ ((p1 → (((p4 → p2) ∨ False) → ((p3 ∧ p1) ∨ True))) ∨ (p4 ∧ p4)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649014448067509819657550773942 : (((((((((p3 → p4) → ((p1 → ((p5 ∧ p5) ∨ False)) → True)) ∧ True) → (p2 ∨ (True ∧ p3))) ∧ (p4 ∨ p2)) → p5) ∧ (True ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43181667753919485592003430816 : (((((False ∧ True) ∨ (p2 ∨ (p3 ∧ ((p3 ∧ (True → (((p5 ∨ False) ∨ (((True → p5) → p5) ∧ False)) ∧ p1))) ∨ p1)))) ∧ p1) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192029860030714562069048693669 : ((p2 → ((True ∨ ((p1 ∨ p5) ∨ False)) ∧ (p1 ∨ p1))) ∨ ((p3 → (p5 ∨ ((True → p5) ∧ p5))) ∨ (True ∨ (((p1 ∨ p1) → p4) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207274178705117584493066527565 : (((((p3 ∨ p1) ∨ True) → p4) ∨ p2) → (((p4 ∧ p3) ∧ (((p5 ∨ p4) → True) ∨ (True ∧ True))) ∨ ((p1 → p1) → (p4 ∨ (p2 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134219603227469582825544598544 : ((((False ∧ ((True → (p1 ∨ p2)) ∨ p4)) ∧ (((p3 ∧ p3) ∧ (p5 ∨ (p3 ∨ False))) → (p1 → (p1 → p4)))) ∨ True) ∨ ((p1 → p3) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353534132119366383788250363007 : (p4 → (p3 ∨ ((((True ∨ (p2 → p3)) ∧ p5) ∨ (p4 → (p3 ∨ ((p1 ∨ False) ∨ (p5 ∧ (((p1 ∨ p4) ∨ (p3 ∨ p3)) → False)))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136242940452792642520190579068 : (((p1 ∧ (((p1 ∨ p3) ∨ p2) ∧ False)) ∨ (p1 ∧ (((p4 ∧ ((p1 → p1) ∧ p5)) ∨ (p1 → True)) ∧ (True → p3)))) ∨ ((False ∧ p4) → p5)) := by
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
theorem thm_5_vars_164480834117945799651770088677 : ((((True ∨ (((p4 ∧ p1) ∨ False) ∨ ((False ∨ (True → (True → p5))) → p2))) ∨ False) ∧ p1) ∨ ((((p4 ∧ p5) → False) ∧ (p1 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194163192764301940059933793653 : ((p2 → ((False ∨ ((p4 ∨ (p2 ∧ p1)) → p1)) ∧ p2)) → (p2 → ((True → ((p2 ∨ p1) ∧ (p4 ∧ ((p5 ∨ False) → (True ∧ p1))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137458438986933891868260889315 : ((p4 ∧ ((True → p5) → (p2 ∨ (((p1 → ((p4 → p3) ∨ (p1 ∨ False))) → ((False ∧ p5) ∨ p5)) ∨ (p4 ∨ p1))))) ∨ (p2 ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3432348368477519568267851773 : (True ∧ (((p1 ∨ p4) ∨ ((False ∧ ((p3 → p3) → (((p4 ∨ (p2 ∧ False)) ∨ (p1 ∧ p1)) ∧ False))) ∨ p1)) ∨ (False → (p5 ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116651315827880995064531579036 : (((p3 → p1) ∧ ((p1 ∧ ((p4 → (p4 → False)) ∧ (p1 → p4))) ∨ (((((p4 ∧ p3) ∨ (p3 ∧ False)) → True) ∨ p3) → p2))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798055857543945029379066555937 : (((p1 → (((((p5 ∨ ((p4 → True) → (False → (p4 → p2)))) ∨ False) ∧ p5) ∨ (p4 ∧ ((p2 ∧ p2) ∨ p2))) ∨ ((p1 → p3) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148899906144860168127191165853 : (((False ∨ (p3 → (p4 ∨ False))) ∨ (False ∨ ((p1 ∨ p1) ∨ ((False ∨ False) → ((p2 ∧ p5) → (p5 ∧ False)))))) ∨ ((p1 ∧ (p4 ∨ p1)) ∧ True)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590738964507447948643297004543 : (((((False ∨ ((p4 ∨ (True ∨ (p2 ∨ (p5 ∧ (p1 ∨ ((((False ∧ True) → p1) ∧ p5) ∧ ((True → p1) → True))))))) ∧ p1)) → p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751448585540234331165746723862 : (((True ∧ ((True → p2) → ((((p1 ∨ p4) ∨ ((p5 → p5) → (False ∧ ((False ∨ (p3 → p2)) ∧ p2)))) ∧ (p3 ∧ p5)) ∨ (False → False)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54783954172662972910389873668 : (((p2 ∧ (p2 → (p1 ∨ (p4 ∧ (p3 ∨ p4))))) → ((((p5 ∧ p3) ∨ (False ∧ (p5 → p5))) ∨ p5) → (((p5 ∧ False) ∧ False) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



