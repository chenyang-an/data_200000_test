variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631908581839249111505545543827 : ((((((p3 → ((False → p2) ∧ p3)) ∧ (((p3 ∧ ((p1 ∨ p1) → p5)) ∨ p3) ∨ (p5 → ((False → p5) → (False ∧ False))))) → False) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197525541241468500144984364750 : (((((False ∧ p5) ∨ p2) ∧ p3) ∨ (p5 → p2)) ∨ (((p4 → (((p4 ∨ p4) ∨ True) ∨ (p1 ∧ p3))) ∨ p4) ∨ (p2 ∧ (False → (p3 ∧ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257816132273311542970078293194 : ((p3 ∨ p5) → ((p3 → ((((True ∧ p3) ∧ (p1 ∧ p5)) ∧ p4) ∨ p1)) ∨ ((p5 → p5) → (False → (((True → (False ∨ True)) → p1) → p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117321019712773029054132787028 : ((False ∧ (((((p1 ∨ False) ∨ (p5 → (False ∧ False))) ∨ p5) ∨ p3) → (p3 ∧ ((p4 → ((p1 → p3) ∨ p4)) ∧ (p3 ∧ p1))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135295720749961372118136487767 : (((((False → p5) ∧ ((False ∨ (((p3 → False) ∨ (p1 ∨ p5)) → p2)) ∨ (p1 ∧ p5))) ∧ False) ∧ (False ∨ (p5 → p5))) ∨ (p3 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343047921592446168844146098532 : (p2 → ((p1 ∨ ((p4 ∨ True) ∧ p1)) → ((p4 ∧ (True ∨ False)) → (((((p1 → ((p3 → p4) ∨ p3)) ∧ p5) ∧ p5) ∨ False) ∨ (p1 ∨ p1))))) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61063639992533940811095356324 : ((False ∧ (((p3 → ((((p4 ∨ (p4 ∧ False)) ∧ p3) ∧ (False ∧ (p3 → (p3 ∧ p1)))) ∧ (p5 ∧ p2))) ∨ True) ∨ (False ∨ (p2 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173335415522607248331491240394 : ((p2 → ((p3 → True) → (((True → True) ∨ ((True ∨ p2) → (p5 ∧ p2))) → p5))) ∨ (((p3 → p4) ∨ (p1 ∧ p1)) ∨ (True ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157203402611570541798711664301 : ((((p1 ∧ (p1 ∨ ((p5 ∧ p1) ∧ ((False ∨ ((p1 ∨ p5) ∧ False)) → True)))) ∨ (p3 ∨ True)) → False) ∨ (p4 ∨ (p1 ∨ ((p4 → p5) → True)))) := by
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
theorem thm_5_vars_658622192266568274187480557639 : ((((p3 ∨ (((False ∧ p2) ∧ p2) ∧ (p3 → (((p2 → p1) ∨ p4) ∨ (((((True → True) ∧ False) → p4) → p5) → p4))))) ∨ (True ∨ p3)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_344187404961168071643949975939 : (p2 → (p1 ∨ ((((p2 ∧ ((p4 ∨ p4) ∨ p3)) ∧ False) ∧ ((p3 → p4) ∧ p5)) ∨ (False → (p4 ∧ (p2 ∧ (p1 ∧ (p1 ∧ (p2 ∧ p5))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
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
theorem thm_5_vars_40078088211221622920152543035 : (((((((((p5 ∧ False) → p3) ∧ ((p3 ∧ ((False ∨ p1) ∧ (p1 → ((p4 ∨ p4) → p3)))) ∧ p1)) ∧ True) → p1) → False) ∧ p4) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142241750986122563782369904252 : ((p2 ∧ (((((((False → (p2 ∧ p5)) ∨ True) ∧ True) → p5) → p5) ∨ ((p1 → p4) ∨ (False ∧ (p3 ∨ p5)))) ∧ True)) → ((p5 ∧ p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166292029554264115409622213072 : ((p4 ∧ (((((p1 → False) ∨ p1) → p1) ∨ p3) ∨ (p2 ∨ (True → (p2 ∨ (p2 ∧ p3)))))) ∨ (((p5 ∧ p3) ∨ (p4 ∨ (p1 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678759846809459190751884318354 : (((((True → p1) → (p3 ∧ (p5 → (p5 → (p5 → (((True ∧ (p3 → False)) ∨ p4) ∨ (p4 ∧ p5))))))) ∨ ((True → (p2 ∧ True)) → p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53977932838368085874310478474 : (((((p5 ∧ ((False ∨ (p1 → True)) ∨ p1)) ∧ p1) ∨ p5) → ((((True → False) ∨ p3) → p2) ∨ ((False ∧ (False ∧ p3)) ∧ (p3 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200767830255147609008630098859 : ((p4 ∧ (((True → p3) → (p1 ∧ p1)) → True)) → (p3 → (p1 ∨ (p3 ∨ ((p3 ∨ p1) ∨ ((p5 → (p1 → (p3 ∨ True))) ∧ (p3 ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173131332515693456388884425711 : ((p2 ∨ (p5 ∨ ((p1 ∧ (p2 ∧ p4)) ∨ (True ∨ (((p2 ∨ p5) ∨ p4) ∧ p3))))) ∨ (p3 ∧ (p5 ∨ (False ∧ (p2 ∧ ((p3 ∧ p1) → True)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_50970325323027688432092850141 : (((((True ∧ (p2 ∨ p3)) ∨ p2) → ((p3 ∧ (p3 ∨ (p1 ∨ (p3 → (p1 → p3))))) ∨ True)) ∧ (p2 → (((p2 ∨ True) ∨ True) → p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184247542645316554098336695165 : ((((True ∧ ((False → p5) → (False ∧ (p4 ∨ True)))) → False) → p3) ∨ (p5 ∨ (False ∨ (p4 ∨ (((True ∧ (False ∨ False)) → False) → (p4 → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194062370610065206750252658221 : ((p5 ∨ (p4 → (p1 ∨ (p4 ∧ ((p5 ∧ p3) ∨ p3))))) → (p2 → (((((p2 → p5) ∧ p3) → (False ∧ (p5 → p5))) ∨ p3) ∨ (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157059418176156077059285544418 : (((p4 ∧ ((p1 ∨ False) ∨ (((p4 ∧ ((True → (False ∧ p4)) ∨ (p1 ∧ p1))) ∨ p5) → p2))) ∨ p2) ∨ ((p4 ∨ (False ∨ (p5 → True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329031617981784329975004716903 : (True → (((p4 ∨ p5) ∧ ((p3 ∨ p4) → p1)) → (p1 ∨ (((((True ∨ p5) ∧ p1) → p1) → (True → p3)) ∨ ((p2 ∧ True) ∨ (True ∨ p2)))))) := by
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
  case inr h6 =>
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
theorem thm_5_vars_111991368735988527937486373732 : (((((True ∧ True) ∧ (p2 ∧ p3)) ∧ (False ∧ (((p3 ∨ ((False ∨ (p4 ∧ False)) ∧ (True → p2))) ∧ (True → p5)) ∨ False))) ∨ False) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147336704402389906186341249980 : (((((p4 → True) → (p3 ∨ ((p4 ∨ ((p3 → p2) ∧ ((p3 ∧ True) → False))) ∧ p3))) ∨ (True ∨ True)) ∨ p5) ∨ ((p2 → (p4 ∧ p2)) → p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256304556813388020349084381536 : ((False ∨ p1) → ((p2 ∧ (p3 ∧ p1)) ∨ ((p5 → p1) → (((((False ∨ p5) → (((p3 ∨ p1) ∧ False) ∧ p2)) ∨ p4) ∧ (True ∧ True)) ∨ p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602768605624866858092042481823 : ((((False ∨ (p2 ∨ ((((p4 → (p3 ∨ p5)) ∧ p1) ∨ ((p1 ∧ False) ∧ (p1 ∨ (p5 ∧ (True → (p5 ∧ (p3 ∧ p1))))))) ∧ True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355541428090671158329600485960 : (p5 → ((((((p1 ∧ (False → True)) → (p1 → (p3 ∨ p4))) ∧ (p4 ∧ ((p5 → True) ∨ True))) → (p4 → (p1 ∧ False))) ∨ p5) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158259945907237045831223017694 : (((True ∧ (p3 ∧ p4)) ∨ ((p1 ∨ ((p4 ∨ True) ∧ (p2 ∨ ((p3 ∨ p5) ∧ False)))) ∧ (False → p2))) ∨ (p5 ∨ (p1 → (False ∨ (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319668519514457176997638744386 : (p4 ∨ (((True ∨ ((False ∨ False) ∨ (p5 → False))) → False) → ((p4 → (((p2 ∨ True) ∧ ((p5 ∨ p5) ∧ (p1 ∨ p5))) ∧ (p1 ∧ p1))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((False ∨ False) ∨ (p5 → False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355847510596629210061795765865 : (p5 → (((((p4 ∧ (p3 ∨ (p2 ∨ p2))) ∧ ((p5 ∨ False) → (True ∨ (p2 → p5)))) ∧ (p5 → p4)) ∧ (p1 ∧ p3)) ∨ (p1 → (p2 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228219132579403367243884392647 : ((p5 ∧ (p2 ∨ p3)) ∨ (p5 ∨ ((((p4 ∧ p1) → p3) → False) ∨ ((p1 → (p3 ∧ p1)) ∨ ((False → (p4 ∧ ((p1 ∨ p2) ∨ False))) ∨ p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46908174276386889426294618005 : ((((((False → p4) ∨ ((True → ((p4 ∨ ((p1 ∨ p2) ∨ (p4 ∧ p2))) → p3)) → p1)) → (False ∧ (p2 ∨ p5))) ∨ p2) ∨ (False → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_487459461027265198965636444 : ((((((p2 ∧ (True ∨ (p5 ∧ ((False → (True → False)) → (p5 ∨ (True ∨ (p2 → p4))))))) ∨ (p3 → p5)) → p2) ∧ p1) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60709074476366583442673403206 : ((True ∧ (((p4 ∨ ((p1 ∧ p2) → p1)) ∧ (p2 ∧ p4)) → ((p4 ∨ (p5 ∧ True)) → ((p3 ∧ (False ∨ (False ∧ p3))) ∧ (p5 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51233839131643913597829275217 : ((((True ∨ (True → (p2 ∨ p4))) → ((((p1 ∧ (p1 → True)) ∨ (False → True)) ∧ p4) → False)) ∨ (p3 ∨ ((p5 ∧ p5) ∨ (True ∨ p4)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_346327355269466318382530250996 : (p3 → (((p1 ∨ ((p5 ∨ (p1 → p5)) ∧ (p4 ∨ (((False → (p2 → p3)) ∨ (p4 → p1)) → p2)))) → ((p5 ∨ False) ∧ False)) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192774333781158699202905633193 : (((p4 ∧ (p1 ∧ (p2 ∧ ((p5 ∧ False) → True)))) → True) → ((p5 ∧ ((p4 ∨ p2) → p4)) ∨ (((p1 ∨ True) → (p3 ∧ (p2 ∧ p2))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68657003061219849630978902670 : ((p4 → (((((p2 → True) ∧ True) ∨ (p2 ∧ p2)) ∧ (((True ∧ p4) ∨ ((((p3 → (p3 ∧ True)) ∧ False) ∧ True) ∧ p5)) → p3)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734331266138151170091407689892 : ((((False ∨ p3) ∧ ((((True ∨ ((p1 ∨ (False → (p4 → (False ∨ False)))) → (p3 ∧ (p3 ∨ (True → p2))))) ∧ p5) ∧ (p2 ∨ p5)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111519003528451095428746616172 : (((p5 → ((p3 → p4) ∨ (p4 → ((True → p3) ∧ ((((p1 → (p4 ∧ p2)) ∧ p1) ∧ p5) ∨ (p1 ∨ (p3 ∧ p5))))))) ∧ p4) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300094120674982009808114232041 : (False ∨ ((((((p4 ∨ ((p4 ∨ p3) ∧ (p4 → (True → True)))) → (True → False)) ∧ p1) ∧ (p4 ∧ True)) ∨ (p2 → (True ∨ True))) ∨ (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321567324617658262927938907263 : (p4 ∨ (p2 → ((True → (p3 ∨ p4)) → (p2 → ((((((False ∧ p1) ∨ p2) ∨ True) → ((p4 ∨ (False → (p3 ∧ p4))) ∧ p4)) → p5) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59832143025935134586590826758 : (((p3 ∧ p2) → (p4 ∧ ((p3 ∧ ((False ∧ (True → ((True ∧ ((p1 ∨ p3) ∧ p1)) → (p3 ∨ (p3 ∨ False))))) ∧ (False ∧ p4))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173354125336110803312908442247 : ((p3 → (((False ∨ p2) ∨ ((p2 → p2) ∧ ((p2 ∨ p4) ∨ p1))) ∧ (p1 ∧ p2))) ∨ (((p2 ∧ ((True ∧ p2) ∧ p5)) ∧ p3) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184247455466430571809927731068 : ((((True ∧ ((p2 ∧ (False ∨ p2)) ∧ (True ∧ p1))) → False) → False) ∨ (p3 → (((((True ∧ p2) → p4) → (True ∧ True)) ∨ (p4 ∨ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_51257192579634006418495493156 : ((((p3 ∧ p4) ∨ (p1 ∧ (False ∨ ((((p2 → (p4 → (p1 ∨ p4))) → True) ∧ False) ∨ True)))) ∨ ((p4 ∨ (False ∨ p1)) → (False → False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201766094763808112196318754341 : ((((p3 → (p3 ∨ p3)) ∨ False) ∨ p4) ∧ (p3 ∨ ((p3 ∨ (((p2 ∧ (False ∨ (p4 ∨ p2))) ∧ (True → p5)) ∨ (True ∨ (p4 ∨ p5)))) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_112830335964050685013212590578 : ((((p1 ∨ ((p2 ∧ True) ∧ p5)) ∨ (((False → ((p4 ∨ p4) ∨ ((((p1 ∨ p1) ∨ p4) → p4) ∨ True))) ∨ p1) ∨ p1)) → p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144786796764621026837795623833 : (((p4 ∧ ((((False ∧ p1) ∨ p3) ∧ (p5 ∧ (True ∧ (p2 → (True ∧ False))))) ∨ False)) ∨ (False → (p5 ∨ True))) ∧ (True ∨ ((True ∨ p2) ∧ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324175204733964728607353203660 : (p5 ∨ (((p3 ∧ p1) ∨ (((p5 → (p5 ∧ p4)) ∧ True) → p4)) ∨ ((p2 → ((False ∨ (p2 ∧ p2)) ∨ (p5 → p3))) ∨ (True ∧ (p1 ∧ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174550411183257413208189419405 : (((((p4 ∧ True) → p3) ∧ p5) ∧ (((True → (p3 → True)) → p2) ∨ (p2 → True))) → (((True ∧ p1) ∨ (p2 ∨ (p3 → p3))) ∨ (p5 → p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594839671042178839893140224665 : (((((((True ∨ (True → ((True ∧ False) ∨ False))) ∧ (p1 ∧ p1)) ∧ (p5 ∨ True)) ∧ ((p2 ∧ False) ∨ ((p3 ∧ (p1 → p1)) → p1))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129124900442052679198350544907 : ((((((False → (False ∧ p2)) ∧ p3) ∨ (((((p2 ∧ False) ∧ (False → (p5 → False))) ∨ True) ∨ p4) ∨ p1)) → False) ∨ True) ∧ ((p4 ∧ p4) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173088547293628476224091557203 : ((p1 ∨ ((((False ∧ (p3 ∧ p3)) ∨ p4) ∧ p5) ∨ (p5 ∨ ((True ∨ True) → True)))) ∨ ((p5 → ((p2 ∧ False) ∧ p1)) ∧ ((p3 ∧ p2) ∧ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156923219455676546661559220197 : ((((p4 ∧ ((p3 → (((((p4 ∨ p1) ∨ p5) ∨ (p2 ∧ p2)) ∧ p2) ∧ p4)) ∧ p3)) → p1) ∨ p2) ∨ ((False ∧ True) → ((p2 ∨ p4) ∨ p5))) := by
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
theorem thm_5_vars_165765326832778268077602279262 : ((((p4 ∨ (p2 ∨ p3)) ∧ True) → ((((p4 ∧ False) ∧ ((False ∧ False) ∧ p3)) ∨ p2) ∨ True)) ∨ (p4 → ((False → ((False ∨ True) ∨ p4)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175277531611730832879080444334 : ((p3 ∨ (((((p4 ∨ (p1 → True)) → (p2 ∨ p4)) → (p4 → p3)) → p4) ∧ True)) → ((((p3 → (p2 ∨ (p4 ∨ False))) ∨ p4) ∨ True) ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49500855711506886407380552361 : ((((p5 ∧ ((p5 ∨ ((((p3 ∨ p3) ∨ p3) ∨ (((p2 → p1) → p5) ∨ p1)) ∧ (p3 ∧ p5))) → p5)) → p5) → ((p4 ∨ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111943182768114729844954604043 : (((((p1 ∧ p3) → (p3 → (p4 ∧ (True ∧ (p2 ∨ p3))))) → (p3 ∧ ((((p1 ∨ False) ∨ (p4 → p4)) → p1) → p5))) ∨ p5) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172691477645521217495082017677 : (((p3 ∧ p1) ∨ ((p3 ∧ (p3 → (True ∧ ((p1 ∧ p3) ∧ False)))) ∨ (p5 ∨ False))) ∨ (((False ∨ p1) ∧ p4) ∨ ((False → (p1 → p1)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49602848713437013145376611288 : (((((p3 → (((p5 ∧ p4) → p3) → (p4 → p1))) ∨ p1) ∨ (p5 ∨ (((p1 → False) ∨ (p3 ∨ p5)) ∧ p5))) → (p5 ∧ (p2 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136989770127705714204790438058 : (((p5 ∧ p1) → ((p4 → (p1 ∨ p2)) → ((p4 ∧ p4) ∧ ((p2 ∨ (p1 ∨ (((p5 ∧ p1) ∨ p4) → p4))) ∧ p4)))) ∨ ((p3 ∧ False) → p4)) := by
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
theorem thm_5_vars_53913724677223008308367876076 : (((False ∨ ((p3 ∨ ((p5 ∨ p4) ∧ p2)) ∨ (True → p5))) ∨ (True ∨ (p3 ∨ ((p5 ∨ (True ∨ ((p5 ∧ (p4 ∨ True)) → p3))) ∨ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134827249312845614917941564785 : (((p1 ∨ (((True ∨ ((p1 ∧ p3) ∨ p2)) ∨ p5) → ((p2 ∧ (p4 → p4)) ∨ (p4 ∨ ((p5 ∧ p4) → False))))) → p2) ∨ (False → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341684412866778546123086476196 : (p2 → (((((p4 ∧ (p2 ∨ (True ∧ (p5 → True)))) ∨ p2) ∧ (((True ∧ p4) ∨ p3) → (((p2 ∨ p1) → p5) ∨ p2))) → p1) ∨ (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323906980375170977400173683132 : (p5 ∨ ((True ∧ (((p4 ∨ (((True ∧ False) → p1) ∧ True)) ∨ (p3 ∧ (p5 ∧ p4))) → p5)) ∨ ((True ∧ ((p2 → (True ∨ p1)) → p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135578974151491445549254514196 : ((((p5 ∧ (((True → True) → p4) ∧ (p3 ∨ (p1 → (p2 ∧ (p2 ∧ p5)))))) ∨ p2) ∨ (((p2 → p2) → True) → p1)) ∨ ((p4 → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768063133026621934484650066875 : (((p5 ∧ ((p2 ∧ ((((p4 ∨ p3) ∨ ((p2 ∧ (True → True)) → (p4 ∨ p1))) ∧ ((True ∧ p2) ∧ (p2 ∧ p1))) ∨ p1)) ∧ (p2 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234743135221237604847235741409 : ((p4 → (False → p5)) → ((((((True → ((((p3 ∨ p5) ∨ (False → p1)) ∨ p1) → True)) → p1) → p4) ∧ p1) ∨ True) ∨ ((p3 ∨ p3) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684979684083469325091752519945 : ((((p3 ∧ (True → (((p5 ∧ ((p4 → (True ∧ p3)) ∧ ((p5 → p2) ∨ False))) ∨ p4) → p3))) ∨ (p3 ∨ ((p2 → (p2 ∨ p2)) ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124723258530895301432668073919 : ((((p2 ∧ (False → p4)) ∨ p5) ∧ ((((False ∨ ((p4 ∧ p4) ∨ p4)) ∧ p2) ∧ (((p1 ∨ p5) ∧ p5) ∨ p1)) ∧ (True → False))) → (False ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h21 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h22 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h23 := h8 h22
            -- False on the left can always be used.
            apply False.elim h23
          case inr h24 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h25 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h26 := h8 h25
            -- False on the left can always be used.
            apply False.elim h26
        case inr h27 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h28 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h29 := h8 h28
          -- False on the left can always be used.
          apply False.elim h29
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h34 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h35 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h36 := h8 h35
            -- False on the left can always be used.
            apply False.elim h36
          case inr h37 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h38 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h39 := h8 h38
            -- False on the left can always be used.
            apply False.elim h39
        case inr h40 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h41 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h42 := h8 h41
          -- False on the left can always be used.
          apply False.elim h42
  case inr h43 =>
    -- Conjunctions on the left can always be decomposed.
    let h44 := h3.left
    let h45 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h46 := h44.left
    let h47 := h44.right
    -- Conjunctions on the left can always be decomposed.
    let h48 := h46.left
    let h49 := h46.right
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h50 =>
      -- False on the left can always be used.
      apply False.elim h50
    case inr h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h55 =>
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h58 =>
            -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
            have h59 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h45, we can now drive its conclusion.
            let h60 := h45 h59
            -- False on the left can always be used.
            apply False.elim h60
          case inr h61 =>
            -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
            have h62 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h45, we can now drive its conclusion.
            let h63 := h45 h62
            -- False on the left can always be used.
            apply False.elim h63
        case inr h64 =>
          -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
          have h65 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h45, we can now drive its conclusion.
          let h66 := h45 h65
          -- False on the left can always be used.
          apply False.elim h66
      case inr h67 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h68 =>
          -- Conjunctions on the left can always be decomposed.
          let h69 := h68.left
          let h70 := h68.right
          -- Disjunctions on the left can always be decomposed.
          cases h69
          case inl h71 =>
            -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
            have h72 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h45, we can now drive its conclusion.
            let h73 := h45 h72
            -- False on the left can always be used.
            apply False.elim h73
          case inr h74 =>
            -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
            have h75 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h45, we can now drive its conclusion.
            let h76 := h45 h75
            -- False on the left can always be used.
            apply False.elim h76
        case inr h77 =>
          -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
          have h78 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h45, we can now drive its conclusion.
          let h79 := h45 h78
          -- False on the left can always be used.
          apply False.elim h79
  -- Conjunctions on the left can always be decomposed.
  let h80 := h1.left
  let h81 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h80
  case inl h82 =>
    -- Conjunctions on the left can always be decomposed.
    let h83 := h82.left
    let h84 := h82.right
    -- Conjunctions on the left can always be decomposed.
    let h85 := h81.left
    let h86 := h81.right
    -- Conjunctions on the left can always be decomposed.
    let h87 := h85.left
    let h88 := h85.right
    -- Conjunctions on the left can always be decomposed.
    let h89 := h87.left
    let h90 := h87.right
    -- Disjunctions on the left can always be decomposed.
    cases h89
    case inl h91 =>
      -- False on the left can always be used.
      apply False.elim h91
    case inr h92 =>
      -- Disjunctions on the left can always be decomposed.
      cases h92
      case inl h93 =>
        -- Conjunctions on the left can always be decomposed.
        let h94 := h93.left
        let h95 := h93.right
        -- Disjunctions on the left can always be decomposed.
        cases h88
        case inl h96 =>
          -- Conjunctions on the left can always be decomposed.
          let h97 := h96.left
          let h98 := h96.right
          -- Disjunctions on the left can always be decomposed.
          cases h97
          case inl h99 =>
            -- We want to use the implication h86 based on <expert-advice>. So we show its premise.
            have h100 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h86, we can now drive its conclusion.
            let h101 := h86 h100
            -- False on the left can always be used.
            apply False.elim h101
          case inr h102 =>
            -- We want to use the implication h86 based on <expert-advice>. So we show its premise.
            have h103 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h86, we can now drive its conclusion.
            let h104 := h86 h103
            -- False on the left can always be used.
            apply False.elim h104
        case inr h105 =>
          -- We want to use the implication h86 based on <expert-advice>. So we show its premise.
          have h106 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h86, we can now drive its conclusion.
          let h107 := h86 h106
          -- False on the left can always be used.
          apply False.elim h107
      case inr h108 =>
        -- Disjunctions on the left can always be decomposed.
        cases h88
        case inl h109 =>
          -- Conjunctions on the left can always be decomposed.
          let h110 := h109.left
          let h111 := h109.right
          -- Disjunctions on the left can always be decomposed.
          cases h110
          case inl h112 =>
            -- We want to use the implication h86 based on <expert-advice>. So we show its premise.
            have h113 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h86, we can now drive its conclusion.
            let h114 := h86 h113
            -- False on the left can always be used.
            apply False.elim h114
          case inr h115 =>
            -- We want to use the implication h86 based on <expert-advice>. So we show its premise.
            have h116 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h86, we can now drive its conclusion.
            let h117 := h86 h116
            -- False on the left can always be used.
            apply False.elim h117
        case inr h118 =>
          -- We want to use the implication h86 based on <expert-advice>. So we show its premise.
          have h119 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h86, we can now drive its conclusion.
          let h120 := h86 h119
          -- False on the left can always be used.
          apply False.elim h120
  case inr h121 =>
    -- Conjunctions on the left can always be decomposed.
    let h122 := h81.left
    let h123 := h81.right
    -- Conjunctions on the left can always be decomposed.
    let h124 := h122.left
    let h125 := h122.right
    -- Conjunctions on the left can always be decomposed.
    let h126 := h124.left
    let h127 := h124.right
    -- Disjunctions on the left can always be decomposed.
    cases h126
    case inl h128 =>
      -- False on the left can always be used.
      apply False.elim h128
    case inr h129 =>
      -- Disjunctions on the left can always be decomposed.
      cases h129
      case inl h130 =>
        -- Conjunctions on the left can always be decomposed.
        let h131 := h130.left
        let h132 := h130.right
        -- Disjunctions on the left can always be decomposed.
        cases h125
        case inl h133 =>
          -- Conjunctions on the left can always be decomposed.
          let h134 := h133.left
          let h135 := h133.right
          -- Disjunctions on the left can always be decomposed.
          cases h134
          case inl h136 =>
            -- We want to use the implication h123 based on <expert-advice>. So we show its premise.
            have h137 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h123, we can now drive its conclusion.
            let h138 := h123 h137
            -- False on the left can always be used.
            apply False.elim h138
          case inr h139 =>
            -- We want to use the implication h123 based on <expert-advice>. So we show its premise.
            have h140 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h123, we can now drive its conclusion.
            let h141 := h123 h140
            -- False on the left can always be used.
            apply False.elim h141
        case inr h142 =>
          -- We want to use the implication h123 based on <expert-advice>. So we show its premise.
          have h143 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h123, we can now drive its conclusion.
          let h144 := h123 h143
          -- False on the left can always be used.
          apply False.elim h144
      case inr h145 =>
        -- Disjunctions on the left can always be decomposed.
        cases h125
        case inl h146 =>
          -- Conjunctions on the left can always be decomposed.
          let h147 := h146.left
          let h148 := h146.right
          -- Disjunctions on the left can always be decomposed.
          cases h147
          case inl h149 =>
            -- We want to use the implication h123 based on <expert-advice>. So we show its premise.
            have h150 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h123, we can now drive its conclusion.
            let h151 := h123 h150
            -- False on the left can always be used.
            apply False.elim h151
          case inr h152 =>
            -- We want to use the implication h123 based on <expert-advice>. So we show its premise.
            have h153 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h123, we can now drive its conclusion.
            let h154 := h123 h153
            -- False on the left can always be used.
            apply False.elim h154
        case inr h155 =>
          -- We want to use the implication h123 based on <expert-advice>. So we show its premise.
          have h156 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h123, we can now drive its conclusion.
          let h157 := h123 h156
          -- False on the left can always be used.
          apply False.elim h157



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197971694859761420430626173423 : (((False ∨ p1) ∧ (p1 ∧ ((p4 ∧ p5) → p4))) ∨ (p5 → (p3 → (((True ∨ (((p3 ∧ p5) → p1) ∨ p3)) ∧ ((False → p3) → False)) → False)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h12
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h18 := h5 h16
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779966280917070763072168761065 : (((p2 ∨ ((p2 ∧ ((p1 ∧ ((p2 ∨ ((False → False) ∧ p1)) → ((p1 ∨ p5) → (p5 → ((p1 ∨ p5) → p5))))) → False)) ∧ (p1 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14896648127928917425739774656 : ((((((p2 ∧ (p4 ∧ p2)) → p1) ∧ p4) → ((p4 → (p2 ∧ p3)) ∨ (((p1 ∧ p2) ∧ (p2 ∨ (True ∨ p4))) → p4))) ∨ (p3 ∧ p4)) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266081713228093358245055588040 : (True ∧ (p2 → ((((((p5 ∧ p1) ∨ p2) ∧ p4) ∨ ((p3 ∨ p2) → p2)) ∧ p4) → ((p1 ∨ p3) ∨ (((p2 ∧ p5) ∧ (p3 → p5)) ∨ p4))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172323006124980048666075036366 : ((((p2 ∨ (True → (p3 ∧ True))) ∧ p5) ∧ (((p3 ∧ (p5 ∨ False)) ∧ p1) ∨ p2)) ∨ ((p5 ∧ p1) → (False → (p5 → (p3 → (p1 ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118242319309352660786448921060 : ((p1 ∨ ((((p3 → (((p5 ∧ False) → p3) → ((False ∧ (False → (p4 ∧ (p1 ∨ p4)))) ∨ p2))) ∨ p2) ∧ p5) ∨ (False ∧ p2))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806292482336530432296846976771 : (((p4 → ((((p3 → p3) → (p1 → (p1 ∧ p4))) → (p3 ∧ (True → ((p4 → (True ∨ True)) → ((True ∨ (p2 ∨ True)) ∧ p5))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354829315407470007131299776701 : (p5 → (((p4 ∧ (p5 ∧ p5)) → (((False ∨ (p2 ∧ (p3 ∨ (True ∨ (p3 → p2))))) → False) ∨ (False → (p3 ∧ (p5 → (True ∨ p1)))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751614057734943324895260237132 : (((True ∧ (p2 ∧ ((p1 → (p4 ∨ (True ∨ p4))) → (p2 → ((p2 ∧ p3) ∧ ((((p1 ∨ p4) ∨ (p2 → (p2 → p1))) ∨ True) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314877867523377918752855853579 : (p3 ∨ ((True → (p2 ∧ ((p1 ∨ p1) ∧ ((True → True) ∧ (False ∧ p5))))) → ((p1 ∧ p3) → (((p3 ∨ True) → (p4 ∧ (p4 → True))) ∧ False)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- False on the left can always be used.
    apply False.elim h21
  -- Implications on the right can always be decomposed.
  intro h22
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h23 := h2.left
  let h24 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h25 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h26 := h1 h25
  -- We need to get the right conjuct of h26 based on <expert-advice>.
  let h27 := h26.right
  -- We need to get the right conjuct of h27 based on <expert-advice>.
  let h28 := h27.right
  -- We need to get the right conjuct of h28 based on <expert-advice>.
  let h29 := h28.right
  -- We need to get the left conjuct of h29 based on <expert-advice>.
  let h30 := h29.left
  -- False on the left can always be used.
  apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216325439112029259758671220190 : ((p2 → (p3 ∨ (p1 ∧ p5))) ∨ ((p3 ∧ (p4 → (((p1 ∨ (p5 → (p1 ∧ True))) → ((p2 ∧ True) ∧ ((p3 → p4) ∧ p5))) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55025312150183043357609198012 : (((p1 ∧ (False ∧ ((p1 ∧ True) ∧ p1))) ∧ ((((p2 ∨ p5) ∨ (p5 ∧ (False ∨ ((False ∨ ((p5 ∨ p1) ∧ p4)) ∨ p2)))) ∧ True) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300687477002947789123072207537 : (False ∨ (((p1 ∨ p1) → (((p3 ∧ p5) ∨ ((True ∧ (False ∨ p2)) → (True ∧ True))) ∨ (p4 ∨ p2))) ∨ ((p2 → p1) → ((p5 ∨ p5) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151286366270242975699039701245 : (((p4 ∧ (p3 ∨ (((True → (p1 → (True ∧ (((p4 ∨ p4) ∨ (p4 → p3)) → True)))) ∨ False) → p5))) → p5) → (((p4 ∨ True) → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111585054175461830907192248265 : ((((p5 ∧ (p5 → ((False ∧ p4) ∨ (p3 ∧ (p5 → (((((p4 ∨ p4) ∧ True) ∨ p2) ∨ (False → p4)) ∧ False)))))) ∧ p3) ∨ p3) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112208685857481297265757433504 : (((False ∨ ((True ∨ (((p1 ∧ p3) → (p3 ∧ ((((p1 ∧ p1) ∧ (False ∧ p4)) → p3) ∧ (p2 ∨ p4)))) ∨ False)) → p2)) ∨ True) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246177431080445026881216439403 : ((p4 ∧ p2) ∨ (p2 ∨ (p4 ∨ (((p5 ∨ (p5 ∨ (p4 ∧ (p2 → ((True ∨ ((False ∨ False) ∧ False)) ∨ (p2 ∨ p2)))))) ∨ (p3 ∧ p2)) ∨ True)))) := by
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
theorem thm_5_vars_135533585586896373898770346371 : ((((((p5 → (p2 → (p5 ∧ p5))) ∧ p5) → ((p5 ∧ p1) ∨ p2)) ∨ (False → p4)) ∧ (((p2 ∨ p5) ∨ p4) → p5)) ∨ (p5 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4642614262299456009591012337 : (p5 → ((((p4 ∨ ((((False ∨ ((((p2 ∨ p3) → p3) ∨ (p4 ∧ p5)) ∧ p3)) → p5) ∨ p4) ∨ p5)) ∧ p1) → p3) ∨ (True ∧ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_13933093156606368076337250434 : ((((p2 → (p4 ∨ ((((p3 → True) → (((p1 → p1) → p4) ∨ p1)) ∨ p4) → (p4 ∨ p5)))) ∨ ((p5 → p5) ∨ p5)) ∧ (p1 → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346897258103682487338182376596 : (p3 → ((((p2 ∨ ((p4 → p3) → ((p5 → p2) ∨ p1))) ∨ (p4 ∧ ((False ∨ p4) → p2))) ∨ p3) ∨ (p3 → ((p1 → p5) ∧ (p4 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214354596586996581196575653645 : (((p3 ∨ (p1 → False)) → False) ∨ ((False ∨ (((((p3 → (p4 ∨ p4)) ∨ (p3 ∨ p3)) → (p1 → False)) → p1) ∨ (p3 → p3))) ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321768421222693941702519729700 : (p4 ∨ (p5 → (p2 → ((True → ((p2 ∨ p5) ∧ (p3 ∧ ((p3 ∧ (p2 ∧ p1)) → p4)))) → ((p4 ∧ (((False ∨ p1) → p1) ∨ p4)) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324031838598986034750065124344 : (p5 ∨ ((p3 ∧ (((False ∧ p3) → True) ∨ ((False ∨ (False → p4)) ∧ (p5 → p1)))) → ((((p4 → (p5 ∧ (False ∨ True))) ∨ p4) ∨ True) ∨ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616086553702492559725977839565 : (((((p4 → (p4 ∧ (((((p3 ∧ False) ∧ p1) ∧ p3) ∧ (p5 ∧ p4)) ∧ False))) → ((((p4 → (p2 ∧ p4)) ∧ False) ∧ p1) ∧ p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_40158018462480773712207544584 : (((((p2 ∨ ((True ∨ ((True → True) ∨ p5)) ∧ (True → True))) ∧ (((p5 → p5) ∨ p4) → (p4 → ((p3 → p2) ∨ True)))) ∧ True) ∨ p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42387874045033301469512470209 : (((p4 ∧ ((((p5 → False) ∧ (False ∨ (p2 ∨ True))) → True) ∧ ((p1 ∨ p2) ∧ ((p2 ∨ p3) ∨ (p2 → ((p3 ∧ p2) → p4)))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114740810996129557629404347366 : ((((True → (True → p4)) → ((((p1 ∨ True) → p1) ∨ (p5 ∧ False)) ∧ (False ∧ p4))) → (True ∧ ((p3 → (p2 → p5)) ∨ p2))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



