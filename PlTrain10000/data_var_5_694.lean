variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198353518108687843913118060319 : ((p2 ∧ (p3 ∧ ((p1 → (p4 → p1)) ∧ p3))) ∨ (((False ∨ (p4 → p5)) ∨ (p4 → (True ∧ p3))) ∨ (((p5 → (p5 ∨ True)) ∧ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193966182182407270628890116939 : ((p3 ∨ ((((True ∧ (p4 ∨ p3)) → p5) ∨ p2) ∧ p1)) → ((((((p4 → False) → (p4 ∧ p1)) ∧ (p1 ∧ p4)) ∨ p4) ∧ p2) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181318751983942879812909510519 : ((True ∨ ((p2 ∧ ((p4 → ((p1 → True) ∧ (p5 → p1))) → p2)) → p1)) → (((p4 ∧ (p1 → (p3 → p5))) ∨ (True ∨ p4)) ∨ (p2 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111595690277189128271862969438 : ((((p2 → ((((True ∧ (p1 → p3)) ∨ (p1 ∨ False)) ∨ ((True ∧ ((p5 ∧ p3) ∧ p4)) ∧ (p5 ∨ True))) → p5)) ∧ p5) ∨ p3) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178116679024917275822273673747 : ((((p1 → (((p3 ∧ (True ∧ p5)) ∧ False) ∨ p5)) → (p2 → p1)) → False) ∨ (p1 → ((((True ∧ ((p4 → p5) ∧ p2)) ∨ p3) → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129268394927357542242878230060 : (((((p5 → True) ∧ (p5 ∨ (p1 ∨ p5))) → (((p5 ∧ p1) ∨ (p4 ∧ ((False ∧ p2) ∨ p3))) ∨ (p3 ∨ True))) ∨ p2) ∧ ((p3 → p5) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65295241887707419445977341674 : ((p3 ∨ ((p5 ∨ (p1 ∨ (p2 ∨ (((p2 ∨ p5) ∧ (p1 ∧ (p4 ∧ False))) ∨ ((p1 → ((p3 → p1) → False)) ∧ p1))))) ∨ (False → p2))) ∨ p3) := by
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
theorem thm_5_vars_317871800991774800633049606244 : (p4 ∨ (((p3 ∧ p4) → (((True ∨ p5) ∧ ((p2 ∧ (False ∧ False)) ∨ (p5 ∨ (p5 → (p5 ∧ (p3 → (False → p5))))))) ∧ (True → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207982397251543879943700773747 : ((((p5 → p5) ∧ p1) ∨ (p2 ∧ p1)) → (((True → False) ∨ (p1 ∧ p4)) → ((p4 ∨ p3) ∨ (((p3 ∧ ((p2 → p5) → False)) ∧ p3) ∧ p2)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39390306398424679169144871590 : (((p3 ∧ (p2 → (p5 → ((((p4 → False) ∨ (False ∨ ((p2 ∧ (True ∧ p2)) → p3))) ∧ ((False → (p4 ∨ p4)) ∨ p1)) ∨ p5)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211255070569506687134444142386 : (((p2 ∧ p2) ∨ (p1 → p1)) ∧ ((p1 → (p3 ∨ (((p3 ∨ False) ∨ p2) ∨ (True ∧ (p1 ∨ False))))) ∨ (p4 ∧ (p5 ∨ (p5 ∨ (p2 ∧ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111536733335925027418083580257 : (((((p3 → ((p5 → (((p2 → (p5 ∨ p1)) ∧ p1) → p1)) → (((False ∨ p4) ∨ (False ∨ p5)) ∧ True))) ∨ True) ∧ True) ∨ False) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54818315363068532395970747100 : (((p5 ∨ (((p4 ∨ True) → p3) → (False → p4))) → ((p2 → (p1 ∨ ((p4 ∨ True) ∧ ((p3 ∧ (True ∧ (p5 → p1))) ∧ p3)))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312332633031013845299214322682 : (p2 ∨ (p2 → (False ∨ ((((True ∧ (True ∨ p4)) ∧ False) ∧ ((((p1 ∨ False) ∨ ((p5 ∧ (p1 → (p2 ∧ p4))) ∨ p4)) → False) → p1)) ∨ True)))) := by
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
theorem thm_5_vars_322468738686358012969478221082 : (p5 ∨ (((p2 ∨ (False ∨ p3)) → ((p3 ∨ p2) → (False ∧ (((True ∧ p4) ∧ ((p4 ∧ (((False ∧ p1) → p2) → p1)) ∨ p2)) → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113869612719336760219247879690 : (((p5 → (p4 ∨ ((((p4 → (p5 ∨ p5)) → (p3 ∨ (p2 ∧ ((p1 ∨ (p5 ∨ False)) → p4)))) → False) → True))) → (False ∧ False)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263584849160283919211229631002 : (True ∧ ((False ∨ (((False → (((p1 ∨ p3) → p1) ∨ (p1 ∧ (p3 ∧ (False ∨ (p5 ∨ p4)))))) → p5) ∨ p5)) ∨ (((False → p4) ∧ True) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655400017782112895151834728453 : ((((((p5 ∨ (((p1 ∨ (((p2 → p3) ∨ p5) ∧ p2)) ∨ p5) ∧ p4)) ∧ ((True ∨ (True ∨ False)) ∨ p1)) ∨ (p2 ∨ p2)) ∨ (p2 → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149673687912594597140789536618 : ((p5 ∧ ((((p4 ∧ (p2 ∧ False)) ∨ (p2 ∧ (p5 ∧ (p4 ∨ p1)))) ∧ (p5 ∧ ((True ∧ p1) ∨ True))) ∧ p5)) ∨ (False → (True ∧ (True ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50745860570126181074000320956 : (((p2 ∧ ((p4 → False) → ((((p4 ∧ (p4 ∨ (p4 ∨ True))) ∧ (p1 → p5)) → (p1 ∨ False)) → p2))) → ((p1 → p5) → (p5 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191310552993108301742333722200 : (((p4 → p4) ∧ (p3 ∧ ((False → p4) ∨ (p1 ∨ p5)))) ∨ ((True → (p4 ∧ (p3 ∧ True))) → (((p2 ∧ (p2 → p5)) ∨ (p4 → True)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676695195140563427414461996638 : ((((p5 ∧ (((p3 ∨ p4) ∧ p1) ∧ (((p3 → (p2 → p1)) ∨ (p5 ∨ (p5 → (p3 ∧ p4)))) ∧ p5))) ∧ (p3 → (p5 ∧ (p4 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656367713743346900163869104979 : (((((((p4 → False) → p2) → (p2 ∧ (((p4 ∨ False) → p1) ∨ p4))) → (p4 ∧ (((False → (p3 ∨ p3)) ∨ p5) ∧ p1))) ∨ (True ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_319853267887626023069756107024 : (p4 ∨ (((p1 ∧ (p1 ∧ p3)) ∧ p3) ∨ ((True ∧ ((((((p1 ∨ (p3 → (False ∨ False))) → p5) ∨ p4) → p2) ∨ p2) ∧ p2)) → (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790948419399036671374490399700 : (((p5 ∨ (p5 → (((((True → ((p3 ∨ False) → (p4 ∧ ((p3 → p3) ∨ (True ∨ p5))))) ∧ p4) → ((True ∧ p1) ∧ p3)) ∧ p5) ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37245157804761308784890921441 : ((((True ∧ (((True → (p1 → (p5 ∨ (((p1 ∧ p1) → p3) ∨ p1)))) ∧ ((True ∧ p1) → (p3 ∨ (p4 ∨ False)))) → p4)) ∧ p4) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262893208726725396169691838123 : (True ∧ ((p3 ∨ ((((p2 ∨ p3) → True) → (p4 ∧ ((((p4 ∧ p5) → p2) ∧ False) ∧ True))) ∧ (False → (((False → p1) ∧ p4) ∨ p2)))) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 ∨ p3) → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178353356107925475515535656889 : (((False ∨ (p5 ∨ ((p2 → (p5 ∨ (False ∧ p5))) ∧ True))) ∨ (True ∧ p2)) ∨ ((p2 ∨ True) → (False → ((p3 → True) ∨ ((p1 ∨ True) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336422197411760178805234413232 : (p1 → ((False ∨ (False ∨ ((p2 → p1) ∧ ((p3 → p1) → ((p3 → p5) ∧ ((p5 → ((p1 ∨ p4) ∧ p4)) → (p2 → (False ∧ p5)))))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246278538188016828971397931368 : ((p4 ∧ p4) ∨ (((p4 ∨ ((p4 → (True ∨ p5)) ∨ p5)) → p5) ∨ ((((p2 ∧ p2) → ((False ∧ False) ∧ p4)) → (p2 → (p1 → True))) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314001813068890963915023898412 : (p3 ∨ (((p1 ∨ True) → ((p5 ∧ False) ∨ ((p4 ∨ True) ∨ ((p4 → p5) ∨ (((p1 → (p3 ∧ p3)) ∨ (p4 → p3)) → p5))))) ∨ (p1 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196759799358469589608289232897 : ((((p1 ∨ (p4 ∧ p2)) ∨ (False ∧ p1)) ∧ p3) ∨ (p4 → ((((False → (p5 ∨ False)) ∨ ((True → ((p4 ∨ p4) ∧ p1)) → p1)) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48891943622642993101367331664 : (((p2 → (((p4 ∧ p1) ∨ (((((False ∨ p2) → p1) ∨ p1) → (p1 → ((p1 ∧ p3) → p4))) ∧ p4)) ∨ p2)) ∧ ((p1 ∧ p5) → p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691479990653735020732084898976 : (((((p1 ∧ p2) → (False ∨ ((((p3 ∧ p5) ∧ p5) ∨ (p5 ∧ (p2 ∨ p2))) ∧ p4))) → ((p2 → (((p2 ∧ p2) ∧ p1) ∨ p4)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134394674082204921182343212994 : (((True → (((p3 ∧ (((p4 ∨ p3) ∧ (True ∧ p3)) → ((False → False) ∧ True))) → p2) → ((p3 ∨ p4) ∧ p2))) ∨ True) ∨ (p3 ∨ (False → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714818829036374950978861945475 : ((((p2 ∧ ((p5 ∨ (True ∨ True)) ∧ p4)) → (((p5 ∨ False) → p2) → ((False ∨ ((p5 ∧ False) ∨ (False ∨ (p1 → False)))) ∨ (True → p2)))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145028059354696185010999744624 : ((((True ∨ True) → (p3 ∨ ((p2 → p4) ∧ ((False → True) → p1)))) ∨ (True ∨ ((p5 ∨ (False ∨ p5)) ∧ False))) ∧ ((True ∨ (p5 → p2)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214463381475615478387753282909 : (((True ∧ p3) ∧ (p2 ∨ True)) ∨ (p4 → (p1 ∨ (p1 ∨ ((p4 → (p2 → p2)) ∧ ((p4 ∧ p2) ∨ ((False ∨ (p3 → (p3 ∨ p1))) ∨ p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40305678790691225650766933438 : ((((((False ∧ (p5 ∨ ((p1 ∧ ((p3 ∨ (p2 → p1)) ∧ ((p1 ∧ (False ∧ True)) → p4))) ∨ True))) ∨ (p2 → p5)) ∧ False) ∨ True) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171867347841407884799334929708 : (((p1 ∧ ((False ∧ p5) → (((((p4 → p2) ∧ p3) → False) ∧ p1) → p2))) → p2) ∨ ((p5 ∧ ((p1 ∨ p5) → (p4 → False))) → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213899347023898855641440543972 : (((p4 ∨ (p1 ∨ p4)) ∨ False) ∨ (((p4 → False) ∨ (True → ((p2 ∨ p3) ∨ ((False ∧ ((p1 ∨ (False ∧ (p4 ∨ True))) ∧ p5)) → p2)))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153156779824825892695449795672 : ((p5 ∧ ((p5 → ((p2 ∧ ((((((p2 ∨ False) ∧ p4) ∧ p2) → p2) ∨ p3) → (p2 ∨ False))) → p3)) → p5)) → ((p2 → False) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352262393173223351918080659293 : (p4 → (((p1 ∨ (True ∨ p3)) ∧ p5) → (((((p5 ∧ ((p4 → False) → ((p1 → p5) ∧ (p2 ∧ False)))) ∨ p3) → p4) → False) ∨ (p2 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
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
theorem thm_5_vars_302649064240945764248349771736 : (False ∨ (p2 ∨ ((p3 ∨ (False ∧ p4)) ∨ ((p1 → (p1 ∨ ((p5 ∧ False) ∨ p4))) → (((((p4 ∨ False) ∧ False) ∧ p4) → p1) ∨ (False ∧ p1)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54691521103510812416979265784 : ((((False → ((p1 → (True → p5)) ∨ False)) → p2) → ((((p5 ∨ False) ∧ p3) ∧ p2) ∨ ((p5 → p4) → (p2 ∧ ((True ∨ p5) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213864112344955142700135386830 : (((p1 ∨ (p4 ∧ p3)) ∨ False) ∨ ((False ∧ (True → (p5 → (((True ∧ True) → p4) ∧ p3)))) ∨ (True ∨ (p5 ∧ (p4 ∨ (p4 ∧ (False ∧ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253100542371006057515590067433 : ((True ∧ p4) → (p2 ∨ (p4 ∧ ((p5 ∨ (False ∧ ((False ∧ ((((p2 → p2) ∨ p4) → p1) ∧ (p3 ∧ p5))) ∨ (p5 ∨ p5)))) ∨ (p3 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666440356068061240708433851313 : ((((((p1 → (p3 → (p1 ∧ p1))) ∨ (True → ((p3 → p1) → ((p4 → p2) ∧ True)))) → (False ∨ (p3 ∧ p3))) ∧ ((p5 → False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634064479582391430889546696669 : ((((((((p5 ∨ (p2 ∨ p1)) ∨ (True ∧ p2)) ∨ (p2 → (True ∧ False))) → ((p5 → p5) → (p3 ∨ (p4 → False)))) → (p4 ∧ p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199579972909360614312683311183 : ((((p4 ∨ ((p5 → False) ∧ True)) ∨ False) → True) → ((True ∧ (((True → True) → p1) ∧ ((((False ∧ True) → (False ∨ p2)) ∨ p2) → p1))) → p1)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241467856573473047343941438773 : ((False → p2) ∧ (((True ∧ (p5 ∨ (p4 ∨ (p5 ∧ (p2 ∨ (p2 → False)))))) ∨ (((((p1 ∧ p4) ∨ False) ∧ p2) ∧ p4) → p2)) ∨ (False ∧ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137954364834880098150726050096 : ((p5 ∨ ((((p4 ∨ (p3 → ((p5 ∧ ((False → (p4 ∨ p2)) ∨ p5)) → (False ∧ p5)))) ∧ (False → p1)) → p3) → p4)) ∨ ((p5 ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152792069258944026857589010486 : (((p4 ∧ True) → ((False ∨ (((p2 ∧ (((p5 ∨ p3) → p2) ∨ (False → (p2 ∧ True)))) → False) → p1)) ∨ p2)) → (((p4 → p2) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686465433761239750472165448347 : (((((p1 → (p2 ∧ p5)) ∧ ((True ∨ ((p4 ∨ (p3 → p5)) → (p2 ∧ p4))) ∧ (p3 ∨ p2))) → (((p1 → p4) ∨ (p2 → p4)) ∨ True)) ∨ p5) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115123982162139730801467583973 : ((((((p1 → p2) → True) ∨ (p5 ∧ False)) ∨ (True ∨ (p5 → p1))) → (((p2 ∨ (p1 → p4)) → p5) → (p4 ∨ (False → p3)))) ∨ (p3 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227808004133342324948410015596 : ((p2 ∧ (True ∧ p3)) ∨ (((((((p1 → (p1 ∧ True)) → (p5 ∧ ((p5 ∨ p3) → p5))) → p1) ∧ ((p3 → p2) ∨ p3)) ∨ False) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137938495475725781101453649152 : ((p4 ∨ (p3 → ((p3 → False) → (p2 → ((p1 ∨ (True → p1)) → (p1 ∧ ((p5 ∨ (p2 → (False → p1))) ∧ False))))))) ∨ (p2 ∨ (p1 ∨ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h16
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h19 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h19
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55520104246699538687811210922 : ((((p5 ∨ p3) ∨ ((p3 → False) → p2)) → (((p3 ∧ (p4 ∨ (p1 ∨ (p2 → ((False → False) → p5))))) ∧ (p3 → (True → p2))) → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h10 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h11 := h4 h10
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h13 := h11 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h15
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h18 := h16 h17
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h20
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h28 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h29 := h4 h28
          -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h29, we can now drive its conclusion.
          let h31 := h29 h30
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h33 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h34 := h4 h33
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h35 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h36 := h34 h35
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h37 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h38 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h39 := h4 h38
        -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
        have h40 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h39, we can now drive its conclusion.
        let h41 := h39 h40
        -- One of the premise coincides with the conclusion.
        exact h41
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h45 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h46 := h4 h45
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h47 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h48 := h46 h47
          -- One of the premise coincides with the conclusion.
          exact h48
        case inr h49 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h50 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h49
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h51 := h4 h50
          -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
          have h52 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h51, we can now drive its conclusion.
          let h53 := h51 h52
          -- One of the premise coincides with the conclusion.
          exact h53
      case inr h54 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h55 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h56 := h4 h55
        -- We want to use the implication h56 based on <expert-advice>. So we show its premise.
        have h57 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h56, we can now drive its conclusion.
        let h58 := h56 h57
        -- One of the premise coincides with the conclusion.
        exact h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208819731624634936803957504073 : ((p3 ∧ ((p1 → (p1 → False)) → True)) → (((p5 ∧ True) ∧ (p2 ∧ (True ∧ ((p5 ∧ p1) ∧ ((p3 → (p2 → p4)) ∧ (p2 → p2)))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691846636066158840872062520153 : ((((True → ((p3 ∧ p1) ∧ (((p2 → ((p4 → False) ∨ p5)) → (p4 → p5)) ∧ p4))) → ((True ∧ ((p3 ∧ p4) ∨ (p1 ∧ p3))) → p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304739362651130402601851328706 : (p1 ∨ (((((p3 → p3) → p3) → p1) ∧ (((p2 ∨ p3) ∧ p5) ∧ ((((p1 → p4) ∨ (True ∨ (p4 ∧ p1))) → p1) → p2))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166965808556299884227110600684 : (((p2 ∧ ((p2 ∨ (p2 ∨ ((p5 → False) ∧ (p4 ∨ ((True → False) → p3))))) ∨ p5)) ∧ True) → (p1 ∨ ((((False ∨ p1) → True) ∨ p1) ∧ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h20
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46583108406516207569263747723 : (((False ∧ ((((((True ∧ p3) ∧ (p4 ∧ p1)) ∨ True) ∨ (p4 ∧ ((p5 ∨ p5) → (True ∧ True)))) ∨ p5) → (p1 ∧ p3))) ∧ (p3 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194761007267184036229025779142 : (((p1 ∨ ((p2 ∧ (p1 ∧ p5)) ∨ p3)) ∨ True) ∧ (p2 → ((p4 → False) ∨ ((((p3 ∧ p5) ∧ (False ∧ (False → (p5 ∨ True)))) ∧ p2) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68661937349997781372217062261 : ((p4 → (((p4 → False) ∧ ((p3 → p2) ∧ (p2 → (((False ∨ ((p1 ∨ ((True ∧ p2) → False)) → (p5 ∧ False))) ∨ p4) ∨ p1)))) → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314754225036219673781335870461 : (p3 ∨ ((False ∧ ((((((p5 ∨ p1) ∨ (p5 ∨ p4)) ∨ p5) ∨ p1) → p5) ∧ True)) ∨ (p2 → (((p3 → (p2 ∨ False)) ∨ False) ∨ (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149383584741765520087946159534 : (((p4 → False) → ((False → p1) ∧ (p3 → ((p2 → (p3 ∧ p5)) ∧ (((p1 ∨ p3) → (p2 → False)) ∨ True))))) ∨ (p2 → ((p4 ∧ False) → False))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348058401371298511148564430524 : (p3 → ((p2 ∨ p4) ∨ ((((True ∨ False) ∨ False) → (((((False ∧ p4) → p3) ∨ False) → (False ∨ p3)) → (p5 ∨ ((p2 → p5) ∧ False)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314677477016216810131424914489 : (p3 ∨ (((((p2 ∨ ((p4 ∨ p1) ∨ p5)) ∧ (((p3 → True) ∨ p2) → p2)) → p2) → False) → (p2 ∧ (p2 ∧ (((p4 ∨ p1) ∨ False) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ ((p4 ∨ p1) ∨ p5)) ∧ (((p3 → True) ∨ p2) → p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h10 : ((p3 → True) ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h11
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h12 := h5 h10
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h14 : ((p3 → True) ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h15
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h16 := h5 h14
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h18 : ((p3 → True) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h20 := h5 h18
        -- One of the premise coincides with the conclusion.
        exact h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h2
  -- False on the left can always be used.
  apply False.elim h21
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h22 : (((p2 ∨ ((p4 ∨ p1) ∨ p5)) ∧ (((p3 → True) ∨ p2) → p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
          have h30 : ((p3 → True) ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h31
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h25, we can now drive its conclusion.
          let h32 := h25 h30
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h33 =>
          -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
          have h34 : ((p3 → True) ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h35
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h25, we can now drive its conclusion.
          let h36 := h25 h34
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h37 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h38 : ((p3 → True) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h39
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h40 := h25 h38
        -- One of the premise coincides with the conclusion.
        exact h40
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h41 := h1 h22
  -- False on the left can always be used.
  apply False.elim h41
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h42 : (((p2 ∨ ((p4 ∨ p1) ∨ p5)) ∧ (((p3 → True) ∨ p2) → p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h43
    -- Conjunctions on the left can always be decomposed.
    let h44 := h43.left
    let h45 := h43.right
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h46 =>
      -- One of the premise coincides with the conclusion.
      exact h46
    case inr h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- Disjunctions on the left can always be decomposed.
        cases h48
        case inl h49 =>
          -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
          have h50 : ((p3 → True) ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h51
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h45, we can now drive its conclusion.
          let h52 := h45 h50
          -- One of the premise coincides with the conclusion.
          exact h52
        case inr h53 =>
          -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
          have h54 : ((p3 → True) ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h55
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h45, we can now drive its conclusion.
          let h56 := h45 h54
          -- One of the premise coincides with the conclusion.
          exact h56
      case inr h57 =>
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h58 : ((p3 → True) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h59
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h60 := h45 h58
        -- One of the premise coincides with the conclusion.
        exact h60
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h61 := h1 h42
  -- False on the left can always be used.
  apply False.elim h61
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59567508187629688180418663879 : (((p3 → p4) ∨ (True ∧ ((((p1 → p5) ∨ p5) ∨ ((False ∧ p2) → p4)) → (True ∧ ((p2 → p2) ∧ (((p4 ∧ p4) ∧ p4) → p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52865592656018289202036171855 : (((p2 ∧ (((False → (p5 → False)) → (((True ∧ p1) ∨ True) ∨ False)) ∧ True)) → ((((p4 ∨ False) ∧ p3) ∨ (p2 ∧ (p2 ∧ p1))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117517298454524418035721325182 : ((p2 ∧ ((p4 ∧ (((((p4 ∧ (p5 → ((p2 ∨ p3) → p2))) → (p5 ∧ p2)) ∨ p5) → p1) ∨ (p2 → (p4 ∨ p3)))) ∨ p3)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158446698198649046613320941138 : (((p4 ∨ p1) ∨ (((p4 ∨ (p5 → ((p4 → (p3 ∨ (p3 ∨ p1))) ∧ p2))) → (True ∧ p2)) → False)) ∨ (p3 → (((True ∨ p4) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139830178520071089766882085220 : (((p1 → (((((p1 ∨ (p4 ∨ p2)) ∧ True) ∨ p5) ∧ False) ∨ (False ∧ (((p5 ∨ p4) → p3) → (p5 ∧ p1))))) → False) → ((p4 → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972231910804631666780291952692 : ((((True ∨ p5) → ((((((p3 ∨ p2) → ((p5 → ((p1 → p4) ∨ p5)) ∨ (False ∨ p3))) ∨ False) ∨ ((p4 → p1) → False)) ∨ p3) ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238309171045950753387072764631 : ((False ∨ True) ∧ ((((True → (p3 ∨ ((((True → p4) → (p5 ∧ p4)) ∧ ((p5 → (p4 → p5)) → p5)) ∨ p2))) ∨ True) ∧ p5) ∨ (p3 ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658415410437063442864863631007 : ((((False ∨ (True → ((((p2 → (p1 ∨ ((p2 ∧ p4) ∧ p2))) → (p5 ∨ p4)) → ((p3 ∨ p1) ∨ p4)) ∧ (p2 → False)))) ∨ (p2 → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307335610685357388374145634729 : (p1 ∨ (p3 ∨ ((False ∧ False) ∨ (p3 ∨ ((False ∨ p5) ∨ (((False ∨ False) ∧ ((p4 → p1) → (((p2 ∧ p3) ∨ p1) → p3))) ∨ (False → True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182234037225819464114436495008 : ((((False → (p3 ∨ (p5 ∨ True))) ∧ (p3 ∨ (p2 ∧ p4))) → True) ∧ (p1 → ((p4 ∧ ((p4 → p3) → p2)) ∨ ((True → (p2 ∨ p5)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690217714826568413035258238832 : ((((p4 ∨ (p5 ∨ ((((True → p3) ∧ p2) → ((p3 ∧ p5) ∧ (True → p1))) ∨ p2))) ∨ (True ∨ (p2 ∨ ((p3 → (p5 ∨ True)) ∨ p3)))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_196715699012207812860148399440 : ((((((p4 ∧ p1) ∧ p1) → p1) → p3) ∧ p1) ∨ ((p4 ∧ (p3 ∧ ((p1 ∨ (True → ((p3 → p4) ∧ p2))) ∧ p2))) → ((True ∧ False) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47913468288499830699837738346 : ((((((True → p2) ∧ (p5 ∧ p3)) ∧ ((p2 ∧ (((p4 → p3) ∨ p2) ∧ (p4 ∨ p3))) → (False ∨ False))) → (p5 ∧ p4)) → (p3 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54349051859079052505789673160 : (((p1 ∨ (((True ∧ p3) ∧ p2) ∧ (False ∨ True))) ∧ (True ∧ ((p4 ∧ p3) ∧ ((p5 ∧ (p2 → p3)) ∧ ((p3 ∨ (False → p4)) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226570369890037678091069659547 : (((p4 → p3) ∨ p2) ∨ ((((p4 → p4) ∧ (p4 → p3)) ∧ (p4 ∧ (p3 → (p4 ∨ ((p4 ∧ p4) ∧ True))))) ∨ (p1 → ((p1 → True) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349982563224851491445428467177 : (p4 → (((((p1 ∨ ((((p2 ∨ (True ∧ ((p2 → p4) ∨ p1))) ∧ (True ∨ p4)) ∧ (p5 ∨ p2)) ∨ p4)) ∨ (True → p1)) → p2) ∨ p4) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228208538010713772233490504930 : ((p5 ∧ (False ∨ p4)) ∨ ((True → p4) → ((True ∧ (True → ((False ∨ ((p3 ∨ (p2 ∨ p5)) ∨ p3)) ∨ (p5 → p5)))) → ((True ∨ p1) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h5 := h2.left
    let h6 := h2.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218774465974052796352989139091 : ((p1 ∧ ((p1 → p4) ∨ p2)) → ((p3 ∨ ((False ∧ p4) ∨ (p5 ∧ ((False ∧ (p5 ∨ True)) ∨ p4)))) → (((p1 ∨ p3) → p2) ∨ (p3 → p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h1.left
        let h22 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- One of the premise coincides with the conclusion.
          exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54420002892554053579992279833 : ((((((p3 ∨ (p2 ∨ False)) ∨ p4) ∨ p5) ∨ p4) ∨ (((p2 ∨ (p5 → (p5 → p3))) ∧ (p3 ∨ (p3 → p1))) ∨ ((True ∧ True) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300636250879310721353190913719 : (False ∨ ((((((p1 → (p3 ∧ ((p2 → p3) ∧ p2))) ∨ (p2 ∧ p4)) → p3) → p2) ∨ (p2 → True)) ∧ (p5 ∨ ((False ∧ (p2 ∨ p2)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_632067005927802006368367801394 : ((((((p3 ∨ p2) ∧ (p2 ∨ (((p5 ∧ p3) → (p5 ∧ (p4 ∧ p1))) ∨ (((p3 ∧ False) ∨ (p2 ∨ (False → False))) ∧ p4)))) → False) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66678765473740054776588499844 : ((True → (((True ∧ (p2 ∨ False)) ∨ False) ∨ ((((((p1 ∧ (p3 ∨ (p2 ∨ p3))) ∧ (False ∧ p1)) → p4) ∨ p5) → False) ∨ (True ∧ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246391298642015358898249249348 : ((p5 ∧ True) ∨ (((((((p3 ∨ p4) ∨ ((p2 → True) ∨ (((p3 ∨ True) ∧ True) → p4))) ∨ False) ∧ False) ∨ True) → False) → ((p4 ∧ p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∨ p4) ∨ ((p2 → True) ∨ (((p3 ∨ True) ∧ True) → p4))) ∨ False) ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162027286477015100773663761927 : ((p4 → (((False → p3) ∧ ((p4 → (p3 ∨ (p1 → p4))) → p2)) ∧ ((p1 → (p2 → p2)) ∧ True))) → (((p2 ∨ (p2 → p4)) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253602523239183236445503082662 : ((p1 ∧ True) → (((p1 ∧ (p3 ∨ (((((True ∨ True) ∨ False) → p3) → (p1 ∧ (p1 ∨ p2))) → False))) ∧ ((p5 ∧ p3) → (True → p1))) ∨ True)) := by
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
theorem thm_5_vars_151555463036865427966494285053 : (((((False ∧ p2) ∨ ((True ∧ p3) ∧ (((p5 ∧ p3) → p5) ∨ (p5 ∧ (True → True))))) ∨ True) → (True → p3)) → ((p2 → p5) → (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∧ p2) ∨ ((True ∧ p3) ∧ (((p5 ∧ p3) → p5) ∨ (p5 ∧ (True → True))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165510904991277170932338605756 : ((((False → ((p1 ∨ p2) ∧ ((p2 → p3) → p2))) ∨ True) → (((p5 ∧ p5) → False) → p2)) ∨ (((p2 ∨ (p4 → (p3 ∨ p3))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168953870421821805924114209899 : ((True → (p2 → (p1 → ((p2 → (((False ∧ False) ∧ (False → p5)) → p5)) ∧ (p5 ∧ p3))))) → ((p5 ∨ ((False → p1) ∧ True)) ∨ (True → p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591667844823614790307673091397 : (((((((((((True ∧ p5) ∨ ((True ∨ p3) ∨ p5)) ∨ ((p1 ∨ (p3 → p2)) ∨ p3)) ∧ p1) → False) ∨ p3) ∨ p5) ∨ (p5 → p3)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111107205661568893875327908441 : (((((p5 ∨ (True ∧ (p3 ∧ ((False → p5) ∧ False)))) ∨ False) ∨ (((p1 → (True ∨ p5)) ∨ (p2 ∨ (p1 ∨ p4))) ∨ p3)) ∧ p3) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347508159794580661917136875657 : (p3 → (((p2 → ((p1 → p4) ∨ p5)) ∧ p2) → ((p1 ∧ ((True → p5) ∧ p4)) → (p3 → (p5 ∨ ((False ∧ p5) ∧ ((p5 ∨ p2) ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h11
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h12



