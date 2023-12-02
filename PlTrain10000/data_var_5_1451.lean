variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2404473471584440946679206781 : ((((p4 ∧ p1) ∧ p2) → ((p1 ∧ ((p3 ∨ p3) → p2)) → p4)) → (((p1 ∧ False) ∨ p2) ∨ ((p5 ∧ False) ∨ (p2 → (p2 ∨ p3))))) := by
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
theorem thm_5_vars_244273758010329562953083333025 : ((False ∧ True) ∨ ((p4 ∧ ((p2 ∧ (True ∨ ((False → p4) ∨ False))) → p4)) → ((True ∧ (p1 ∨ ((p1 ∧ (p5 ∧ p3)) ∨ p1))) ∨ (p4 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20249311560525006784284760041 : ((((p3 ∨ (p1 → (True ∧ p5))) ∨ ((p4 ∨ (p4 ∨ p3)) ∨ (p4 ∧ p1))) ∨ ((False ∧ p1) ∨ (False → ((p4 ∧ (p3 ∧ True)) ∨ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157697091984466767914846223059 : ((((p5 → ((((p5 → True) ∨ p3) → ((p2 ∧ p4) ∨ False)) ∨ p2)) ∧ p2) → (p3 ∧ (p4 → p1))) ∨ (((False ∨ False) → p1) ∨ (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_250177241045058223246753083492 : ((True → p5) ∨ (True ∧ ((p4 → (((p5 ∧ p3) ∧ ((p3 ∨ (True ∧ p2)) → False)) → p1)) → ((p1 → p5) ∨ ((p4 ∧ (p2 ∨ p3)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50983922895862463143278935832 : (((((p5 ∨ False) → p1) → ((((p2 ∧ (p3 ∧ (p1 ∧ (False ∧ p4)))) ∨ p1) ∧ p5) ∨ False)) ∧ ((p4 ∧ (p1 ∨ True)) ∨ (p1 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135048660010005478837462776585 : ((((((p2 ∧ p1) ∧ (p5 ∧ p5)) ∧ ((((p4 ∧ (p5 ∧ p4)) ∧ (p2 → True)) ∨ p4) → p1)) ∨ False) ∨ (p1 ∨ False)) ∨ ((False → p1) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1650823039946043497788281101 : (((True → False) ∧ (((p1 ∧ p4) → (((p2 ∨ True) ∧ (p2 ∨ False)) ∧ p1)) ∧ (((p4 ∨ p1) → (p4 ∧ True)) ∧ True))) → (p1 ∨ p3)) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204338747383436467093751260466 : (((p5 ∧ (p2 ∧ (p2 ∧ p1))) ∧ p2) ∨ (False → (((((True → ((p2 → False) ∧ p1)) → (p3 → p2)) ∧ (p1 → p5)) → True) → (p3 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53217400911994384874562786354 : (((((((p2 → p2) → p5) → p4) → p5) → (False ∧ (p1 ∨ True))) ∨ ((((p3 ∧ (False ∨ (p4 ∨ p2))) ∨ p4) ∧ (False ∨ True)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52372326613386605677983190976 : (((((((p2 ∧ True) ∧ (True ∨ p3)) → p2) ∨ p5) ∧ ((p5 → p3) ∧ p1)) ∧ ((p4 ∨ (False ∧ (True → p1))) ∧ (p1 ∨ (False → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804337905014129128297600092042 : (((p3 → ((((p2 ∧ (((True ∧ p1) ∧ p4) ∨ p1)) ∧ (p2 ∧ p5)) → p4) ∨ ((p3 → ((p4 ∧ p2) ∧ ((p2 → p5) ∨ p3))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54679170206952541572391560883 : ((((((True ∧ p5) ∨ False) ∨ (False ∨ p4)) → p4) → (p5 ∧ (((((False → (p4 ∧ True)) ∨ p1) ∨ (p3 → p2)) → p5) → (p3 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50485259521721500815059967939 : (((p3 → ((p3 ∨ p1) ∧ ((p4 → ((True ∨ True) ∧ p3)) → ((p4 ∧ p3) ∧ (p4 ∨ (True → p1)))))) ∨ ((False ∧ (p3 ∨ p5)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328529983543144819646005787560 : (True → ((True ∧ (((((p1 → False) ∧ p5) → True) ∧ ((p3 → (p4 ∨ p3)) ∧ False)) ∨ p3)) ∨ (p4 ∨ (p1 ∨ ((p3 ∨ False) → (p1 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263577746967710349371010847855 : (True ∧ (((p2 ∨ p1) ∨ (False ∨ ((p4 ∧ (p1 ∨ ((p4 → (((p1 ∨ False) ∧ p2) ∧ p3)) → p3))) ∧ p4))) ∨ ((False ∧ p2) → (p1 ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_136205046412651672720821708893 : (((p2 ∨ (p3 ∨ ((p3 → True) → p5))) ∧ ((((p2 ∨ (p3 ∨ p4)) ∨ (p4 ∧ ((False ∧ p4) → p1))) ∧ False) ∨ p3)) ∨ ((True → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225383289901321175923003739020 : (((p2 ∨ p2) ∧ p1) ∨ ((p2 ∧ p2) ∨ (p5 → ((p5 ∧ ((((p3 → False) ∧ (p5 → (p4 ∨ p3))) ∧ (False ∨ True)) → (p2 ∨ p4))) ∨ True)))) := by
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
theorem thm_5_vars_40423311457575186728878752481 : ((((((p1 → (((((p2 ∧ False) ∧ (False → p3)) → p1) ∨ p2) ∨ False)) → p4) → ((p2 → (True ∧ (p1 ∧ True))) ∨ p2)) ∨ p1) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136636522913105827995861164739 : ((((p2 → p2) ∨ p4) → ((p1 ∨ (False ∨ (((p2 ∧ p5) → (p3 ∨ ((p3 → (p4 ∨ p1)) ∧ False))) ∧ p5))) ∧ p1)) ∨ (True ∨ (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190314381080782122040070135284 : ((((p1 ∧ ((p4 → p3) ∧ p4)) ∧ (p1 ∧ p2)) ∨ p1) ∨ (((p4 ∨ p2) ∧ p4) ∨ ((True ∨ p3) ∨ (((p5 ∧ p2) ∧ (p5 ∧ p5)) → True)))) := by
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
theorem thm_5_vars_241714193071545014384013799813 : ((p1 → True) ∧ (((p1 ∧ (((p4 ∧ p3) ∧ ((p1 ∨ p3) ∧ p5)) ∧ ((p4 ∧ (p1 ∧ (p5 → False))) → p4))) ∨ True) ∨ (p4 ∧ (p4 → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301840611031701044767199571841 : (False ∨ ((p4 ∨ p5) ∨ (p1 → (((p2 ∨ ((p1 ∧ ((False ∨ False) ∧ p1)) ∨ ((p5 ∨ p2) ∨ p5))) → p5) ∨ (False → (p1 ∧ (p4 → p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133729138647457645061468329819 : ((((((((p3 → p1) → (p4 → p4)) → p3) ∨ p1) ∧ p4) ∧ (((False ∧ True) → p1) ∧ (p3 ∧ (False ∧ True)))) ∧ p1) ∨ (True ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153592053090543803822138087794 : ((False → (((p1 → False) ∧ p3) ∨ (p1 → (((False → p1) ∨ ((False → (p2 ∧ p3)) ∨ (p2 → p2))) ∧ p4)))) → (((False ∨ p2) ∨ False) → p2)) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314642861157043773069266616376 : (p3 ∨ (((((True → False) ∧ p1) ∨ ((p2 ∨ (p5 ∨ p3)) ∨ ((p4 ∨ p1) ∧ p2))) ∨ p1) ∨ (((p1 ∨ (p5 → p4)) → True) ∧ (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335772604726126955178185758289 : (p1 → ((((p5 → (True → ((p2 ∧ (p3 ∨ ((p2 → (p5 ∧ (False → True))) → (True ∨ (p5 ∧ p1))))) ∨ p1))) → p5) ∨ (True ∨ False)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87271727308036165062155137923 : (((((p4 ∧ (True → p3)) ∧ p4) → p2) ∧ (p2 ∧ (((p1 ∨ (((p3 ∨ ((p2 → p2) ∧ True)) ∨ p5) → p3)) ∧ (p4 → p3)) → p5))) → p2) := by
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
theorem thm_5_vars_52829769326913512045445330398 : (((((False ∨ p3) ∨ False) ∨ (((p3 ∧ False) ∨ (True → (p5 ∨ p2))) ∨ p1)) → (p3 → (p5 ∨ (p4 → (((p2 ∧ p4) ∧ p1) ∨ p3))))) ∨ p1) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180937027550054054240032685281 : (((p5 ∧ p4) ∧ ((p1 ∨ ((((p4 ∧ p1) ∧ True) → p3) ∨ p4)) → p3)) → ((((p1 → (p1 ∨ (True → p4))) ∨ p3) → False) ∨ (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199538147984621786547183982889 : (((((p5 ∧ p5) ∨ (p1 → p5)) ∧ p3) → p4) → (((p4 ∨ p2) ∧ False) ∨ (p4 → ((((p1 ∨ p3) ∧ ((p4 → p5) ∨ True)) ∧ False) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255090611040766326628101209125 : ((p4 ∧ p2) → (((p2 → p1) ∨ p2) → (p4 ∧ (((p4 ∧ (p5 ∨ (((p1 → (p5 ∧ p5)) ∨ (p4 ∧ (p4 ∨ False))) ∧ True))) ∨ p2) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165038458115674260635108009253 : ((((p1 ∨ p5) ∧ (((p3 ∨ p5) ∨ (True → (((p4 → p5) ∨ p4) → p1))) ∧ p5)) → False) ∨ (p2 ∨ (False → ((True ∧ (p4 → p4)) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53798248418820929615294257790 : (((((p3 ∨ (p5 ∧ (p4 → False))) → (True → p4)) → p5) ∨ ((((p4 ∨ p1) → p4) ∨ ((((p1 ∧ p2) → p2) → p1) ∧ p1)) → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216030235204381977646023909036 : ((p5 ∨ ((p1 → p5) ∨ p2)) ∨ ((p3 ∧ ((False ∨ p1) → p3)) → ((((True ∨ p5) ∨ (p3 → p2)) ∧ p2) → (((p4 → p1) ∧ p4) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113190859474194960480286213563 : (((((False ∨ p2) → (p3 ∨ (((p1 ∧ True) ∧ True) → (((p1 ∨ p2) ∨ ((True ∨ p3) → False)) ∧ p5)))) ∧ p4) ∧ (p1 ∨ p2)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37726017862759651258111587372 : ((((((p5 → ((p3 ∧ False) ∧ p2)) → ((p5 ∨ (p2 ∨ False)) → p1)) ∧ ((((False → p2) ∧ False) → True) ∨ (p4 ∨ p2))) → p3) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137413349694608743474299143991 : ((p4 ∧ ((((True → ((p3 ∧ (p4 → (p2 ∨ p2))) ∧ ((p3 → p1) ∧ p5))) ∨ (p4 ∧ p5)) ∧ (p1 ∧ p4)) ∧ p2)) ∨ (False → (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61669453499461334295850194554 : ((p1 ∧ (p4 ∧ (True ∧ (False ∨ (False ∧ (((p1 ∨ p5) → (p1 → (p5 ∧ p1))) → ((p2 ∧ p5) ∧ (((False → False) → p2) ∧ p5)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53741217827327959224632721441 : (((p5 → ((p5 ∧ (p2 → ((False → p4) → False))) ∨ p3)) ∧ (p2 ∧ (True ∧ ((((False ∨ p3) → p5) ∨ p2) ∨ (p5 ∧ (False ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40534262815601744866659011635 : ((((p2 ∨ ((p1 → (((p5 → (p5 ∨ True)) ∨ p3) → p5)) → (((p5 ∨ p5) → (p3 → p1)) ∧ (True ∧ (True ∨ False))))) ∨ True) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159018846830291668208182810474 : ((p4 ∨ ((((p1 → True) → (p2 ∧ (True → p1))) ∨ (True ∨ p5)) ∨ ((False ∨ True) → (True ∨ p4)))) ∨ (True → (((p5 ∨ p1) → False) ∧ p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317603975482446018866355535260 : (p4 ∨ (((p3 ∧ ((p1 ∨ ((p2 → True) → (p5 → ((p3 ∧ p1) ∧ (p5 ∧ (p4 ∧ p2)))))) → ((True ∨ (p4 ∨ p3)) → False))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307449000150221979361030339324 : (p1 ∨ (p5 ∨ ((((p2 → (False → p3)) → True) ∨ (p3 ∧ p4)) → (p4 → (False ∨ ((True ∧ ((False ∨ True) ∨ (True ∨ (False ∧ False)))) ∨ p3)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147825477579782552948531419279 : (((False ∨ (((p4 → ((p3 ∧ (p3 ∨ ((p2 ∨ p2) ∧ (p2 ∧ p4)))) ∧ p3)) → p4) ∧ (p4 → p5))) → p4) ∨ ((p1 → (p1 ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156866522829121267078792067623 : (((((p1 ∨ (True ∨ (p1 ∨ p2))) ∧ ((p3 ∨ p4) ∧ ((False → (p1 ∧ p2)) ∧ p1))) ∧ p1) ∨ True) ∨ ((p3 → True) ∨ (p2 → (True → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184614152040442484593373434331 : ((((p4 → ((p1 ∧ False) ∨ False)) → False) ∧ ((p4 ∨ p4) ∧ p2)) ∨ (p4 → ((p1 ∨ (False ∨ (p4 ∨ (p5 → (True ∨ p3))))) ∨ (p2 → p1)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47486588184852880214082284285 : (((False ∨ ((((((p4 → p4) → True) → (p2 ∨ p4)) ∨ (p4 ∨ (((p5 ∨ False) ∧ p3) ∧ p3))) → p4) ∨ (p3 ∧ p3))) ∨ (False ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58997331400169551921739838845 : (((p3 ∧ p1) ∨ ((False ∨ ((((p2 → p1) ∧ p2) → True) → (((p3 → p2) ∧ (p4 ∨ (p5 ∧ p4))) ∨ (True ∨ p3)))) ∨ (True ∧ p5))) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52173398137090428224734672410 : ((((p4 ∧ (((p4 → False) → p4) → True)) ∧ (((True ∨ (False → p3)) → p5) → p2)) → (p5 → ((p4 ∧ (p2 ∧ p2)) ∨ (True ∧ True)))) ∨ p4) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48057188837743170245654577125 : ((((((p2 ∨ False) ∧ (p5 ∨ (p3 ∧ False))) ∨ p1) ∨ (False → ((p4 ∧ (p4 → (p4 → p3))) ∨ (True ∨ (False ∧ p4))))) → (p5 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64931933289531158569744977622 : ((p2 ∨ (((((p2 ∧ p5) → p1) ∨ (p1 ∨ (p2 ∨ (p3 ∧ (True ∨ p4))))) ∨ p2) → (p5 ∨ ((p2 ∨ (p3 ∧ p1)) ∨ (True ∨ p1))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232140112732765223050550895813 : (((True → True) → p5) → (p4 → ((((p4 → (p5 ∧ (p3 ∨ p4))) → ((p3 → p3) → p5)) → ((p1 ∧ p5) ∧ (p2 → (True ∧ True)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209131687751296284428797993167 : ((p3 ∨ (((p3 → True) → p3) ∧ p5)) → ((p3 ∨ (p2 ∨ p1)) → (((p3 ∨ ((p2 → (p5 → p3)) ∧ (True → (False ∨ p2)))) ∧ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h14 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h16 := h12 h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h22 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h24 := h20 h22
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134159208212729999976550506858 : (((((p5 ∧ ((True ∧ (True → p2)) ∧ True)) → (p4 ∨ (p2 ∧ (p1 ∧ (p3 ∨ p2))))) → (p1 ∨ (p3 ∨ p4))) ∨ True) ∨ ((False ∧ p5) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117068002737153388823007346108 : (((True → False) → ((p3 ∧ (((p4 → ((p1 ∨ ((p3 → (p5 → p4)) ∧ p4)) ∨ (p4 ∨ (p2 ∨ p1)))) ∨ p2) ∨ False)) ∨ p5)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69170159050550853371191072039 : ((p5 → (((((p3 ∨ (p3 ∧ p2)) ∨ p3) → (((p3 ∨ True) ∧ p1) → False)) ∨ (False → p1)) ∨ (p2 ∨ ((p1 ∨ (p3 ∨ False)) ∧ p3)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133706470777634220918992148613 : (((((((p5 → p3) ∨ p4) → (p4 ∨ (p2 ∨ ((p5 ∧ False) → True)))) → p1) ∨ (((p2 → p5) → p2) → False)) ∧ p5) ∨ (True ∨ (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257305312129164776752068006601 : ((p2 ∨ p4) → (((((p1 ∧ ((True ∨ p2) ∨ (p4 ∧ (p4 ∧ (p5 ∨ p1))))) ∨ (((p1 ∨ p5) → p2) ∨ (p5 ∨ True))) ∨ p4) ∨ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157159683786628017404634579008 : ((((p4 ∧ ((((((p1 → p1) ∨ (False → p2)) ∧ p4) ∨ p5) ∨ p1) ∧ (False → p1))) ∨ p3) → p5) ∨ ((p2 → (False ∨ (False → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41678323947965710800944449897 : (((((p3 → p3) ∧ (True ∧ (p5 ∨ p2))) ∨ (p2 → (((((p4 → True) → p4) ∧ (True → False)) ∨ ((p5 → p1) ∧ True)) ∨ p2))) ∨ p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245856629651520541325104945491 : ((p3 ∧ p4) ∨ (((p5 → (p4 ∧ p2)) → False) ∨ (p4 → (((((True → ((True → p4) ∨ (p3 ∧ p2))) ∨ (p2 ∨ p2)) ∨ p2) → False) ∨ True)))) := by
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
theorem thm_5_vars_65133194076420548751439821283 : ((p2 ∨ (p1 → (True → (((p5 ∨ ((p3 ∨ p1) ∨ (p4 ∧ (p3 → True)))) ∧ True) → (True → ((((p1 ∧ False) ∧ p1) ∨ p1) ∧ True)))))) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115109236763967899559566525549 : ((((p4 → (((False ∧ (p1 → p5)) ∨ p2) ∨ (True → True))) ∨ p2) → ((p3 → (p1 → (p4 → (p3 ∨ (p5 ∨ True))))) ∧ p3)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55287802286991310823991627864 : (((p1 ∧ (p3 ∨ ((p3 ∨ False) ∧ p5))) ∨ (((p4 ∨ p2) → (p5 → (True ∨ (p3 ∧ (p3 → (((p1 → p4) ∧ p1) → False)))))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742814753749700017439570761811 : ((((p3 → p1) ∨ ((p2 ∧ p4) ∧ ((p2 ∧ (p3 ∧ (True → True))) ∧ (True → (((False ∧ (p3 → (True → p5))) ∨ p2) ∧ (True → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115138558376267765819131444149 : ((((p4 ∧ p1) → ((p1 ∧ ((p1 → p2) ∧ p1)) ∨ (p4 ∧ p2))) → (((p4 ∧ p1) ∧ (True ∧ p1)) → ((p2 → p3) ∨ p2))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798572688082259130469171235185 : (((p1 → ((True ∨ (True ∧ (p4 ∨ (p3 ∨ p4)))) ∧ (p5 → (p3 → ((((p2 ∧ p2) → ((p5 ∧ p4) ∧ p4)) → p2) ∨ (True ∨ p4)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50840134153132515860674872139 : (((((True ∨ False) → ((True ∨ ((p5 ∨ (p5 → True)) → ((p3 ∨ False) ∨ p2))) ∨ p5)) ∧ p3) ∧ ((True ∧ p4) ∧ ((p3 ∧ p3) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51087652232072448961526338399 : ((((((p4 → (p4 ∧ ((((p4 → p5) ∨ p1) ∨ p3) ∨ (p1 ∧ p1)))) → p2) ∨ p4) ∧ False) ∨ (((p2 ∨ (False ∨ False)) ∧ False) → p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353975518322137784798775070612 : (p4 → (p3 → (((p3 ∨ ((p2 ∨ p2) ∧ (False ∨ (p3 → (p5 → ((p2 ∨ p1) ∧ False)))))) → (p5 ∧ p1)) ∨ (((False ∧ p5) ∧ p1) → p2)))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777872647535810397929819859510 : (((p1 ∨ (((p5 ∨ (False ∨ p4)) → True) → ((p4 ∨ p5) ∨ (((True ∧ ((((p3 → (p3 → False)) → True) ∨ p1) → p1)) ∧ True) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66404341732469269105905646108 : ((p5 ∨ (p1 → ((False ∨ (((((p1 ∧ p4) ∧ p4) ∨ (p5 ∨ (p2 → ((True → p4) ∧ False)))) → ((p1 ∧ True) → p1)) → p3)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163789258265106049397067278433 : ((True ∧ (p1 → (((False ∧ (p1 ∧ (p4 ∨ p3))) ∨ (p5 → (p4 ∨ p1))) ∧ (True ∨ True)))) ∧ (((False → (False ∧ p3)) → False) → (p2 ∧ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → (False ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (False → (False ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66349385152967646253820012080 : ((p5 ∨ (p5 ∧ (((False ∨ (((p3 ∨ p3) → True) ∧ p1)) → (p3 → ((p5 ∨ (p4 ∨ p3)) → (p2 → p5)))) → (True ∧ (False ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347854381058273345633715886463 : (p3 → ((p3 ∧ (p1 → True)) → ((((p2 → (((p2 → p3) ∧ p1) → ((True → ((p2 ∨ p4) ∧ False)) ∨ p5))) ∧ (False → p5)) ∨ p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136091017942789758744090016942 : ((((False ∧ (p2 ∨ (False ∧ (p1 ∨ p2)))) ∧ True) ∨ (p3 → (p2 ∨ (False → (p1 → (True → (p4 ∨ (p1 → p4)))))))) ∨ (p1 ∨ (p3 ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180925020568754874550187454957 : (((p1 ∧ p4) ∧ ((False ∧ ((True → False) ∨ ((False → p5) ∧ p2))) → False)) → (((p2 ∧ True) ∧ ((p3 → True) → (p2 ∧ p3))) → (p3 ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h11 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h13 := h4 h11
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62887518705812075349686262812 : ((p4 ∧ ((False → p1) ∧ ((((((p4 ∧ p4) ∧ True) → (False ∧ p1)) ∨ (p3 → p3)) ∧ (((p1 ∨ (p2 ∨ p5)) → p2) ∧ p1)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205565921300333770909244728419 : (((True → p2) ∧ (p5 → (p4 → p2))) ∨ ((((p4 → p3) ∨ (False ∨ ((True ∨ (p4 ∧ (((p3 → p5) ∧ p5) ∨ True))) ∨ p4))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723098352561311598004836092747 : (((((p4 ∨ False) ∨ p2) ∧ (p5 ∧ (p2 ∨ ((p1 ∧ p3) ∧ (((True ∧ p3) → ((p1 ∨ p1) ∧ (p5 → p5))) ∧ ((p3 → False) ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62116761702076497764145368389 : ((p2 ∧ (p1 ∨ ((p1 ∨ p2) ∨ (((p2 ∨ p1) ∨ (p4 → p3)) → ((p3 ∨ (p2 → (p4 ∨ p2))) ∨ (p4 ∨ ((p5 ∨ p1) → True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46981710185156849073369803746 : (((((p5 ∧ (p3 ∨ ((p4 → ((p3 ∧ True) ∧ (p2 ∨ True))) → (p4 ∨ (p2 ∧ (p1 ∨ p2)))))) → (p5 ∨ False)) → p3) ∨ (p5 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178516231010279451133850942006 : ((((p2 ∨ (((p1 ∨ p4) ∨ p1) → True)) ∨ False) → ((p2 → False) → p5)) ∨ ((p4 → (((p5 ∧ (False → p3)) ∨ p3) ∨ (p1 → p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158154726536073408984849128578 : (((p5 ∨ (p1 ∧ (p4 ∧ p3))) ∨ ((p1 → ((p5 → p3) ∨ p4)) → (True → ((p2 → p4) → p1)))) ∨ ((((p1 → p1) → p3) → p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46011144758498599968527947183 : ((((((p3 → (p2 ∨ (p5 ∧ ((True ∨ False) → p3)))) ∧ True) → ((((p4 ∨ p2) → p1) ∨ p4) ∨ (p4 ∨ False))) ∧ True) ∧ (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112646195296196566049626214200 : (((((((((p3 → p2) ∧ p2) ∨ p4) ∧ (((p2 ∧ (p1 ∧ p2)) → p4) ∨ p4)) → p5) ∧ p5) ∧ (True ∨ (p3 ∧ p4))) → p2) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135811032742511533210767410727 : (((p5 → ((False ∧ (True ∨ p5)) ∨ (p4 → (((p2 ∧ p4) ∨ p2) ∧ p5)))) → (p1 ∨ (((p2 → p5) → p5) ∧ p2))) ∨ ((p5 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114652530795799399600804232886 : ((((p5 ∨ (((p1 ∨ p3) ∨ False) ∨ (p5 → False))) ∧ (p1 → ((p1 ∨ p4) ∧ p5))) ∨ ((True → (False → p5)) ∧ (p2 → p2))) ∨ (p2 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171341669039303788825583632135 : ((((((((True ∨ False) ∧ p3) ∧ p5) ∧ (p2 ∧ True)) ∨ (p1 ∨ p1)) → p3) ∧ False) ∨ ((p1 ∨ (p3 ∨ (p1 ∨ p2))) → (p4 ∨ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54494589133680728962089507833 : (((((p5 ∨ p1) ∧ False) ∧ ((p1 → True) → p3)) ∨ ((p3 → p3) ∨ (True → (((False ∧ (p3 → p1)) → (p4 ∨ p1)) ∨ (p4 → p5))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207670541757413983212943503057 : ((((True → p2) ∨ (False → False)) → False) → ((p3 ∧ ((((p2 ∧ (((p4 ∧ p4) → p1) ∨ p4)) → p2) ∧ (p4 → (p4 ∨ p2))) ∧ p3)) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((True → p2) ∨ (False → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638502600209497043735972513368 : ((((((p3 ∧ ((p1 ∨ p2) ∨ p3)) → p3) ∨ ((False ∧ ((p5 ∧ p5) → (((p5 → False) ∨ (True ∨ (True ∨ p4))) ∧ p4))) → p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191004801447932430382909721880 : (((p2 ∧ (p4 ∧ (p2 → False))) ∨ ((p4 → p2) ∧ p5)) ∨ ((p5 ∧ p3) → ((p2 ∧ ((p4 ∨ p1) ∧ (False ∨ p5))) → (p5 → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148958320870005677257161036247 : ((((False ∧ True) ∨ p5) ∧ ((((False ∨ p5) → (((p2 → p1) ∨ (p3 ∨ True)) ∧ p1)) ∧ p3) → (True ∧ p1))) ∨ (p3 → (p2 ∨ (p4 → p4)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55985832410222779367060284331 : ((((p5 ∧ (True ∨ p4)) ∧ False) ∨ ((True ∧ False) ∧ ((p1 ∧ ((((p3 ∧ ((True ∨ p4) ∧ False)) ∨ p3) → True) → p5)) ∧ (p4 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303748960170071946159935146759 : (p1 ∨ (((((p2 ∧ (((p4 ∨ (p2 ∨ p5)) ∧ p1) → (p5 ∧ p1))) ∧ ((p4 ∨ ((p2 → p4) ∧ p4)) ∧ (p1 ∧ p1))) ∨ False) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719477076399781606775032734703 : ((((p2 ∨ ((p4 ∧ p4) ∧ p5)) ∨ (((p1 ∧ (p1 → ((False ∨ (p3 ∨ p4)) ∧ False))) ∨ p3) ∨ (False → (((False ∧ p2) ∨ False) → p4)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244484315102602562360917872893 : ((False ∧ p2) ∨ (p4 → (p5 → ((((True ∧ (p4 ∨ ((p2 → ((p2 ∧ p2) ∨ (p2 ∧ p4))) ∨ (p1 → (p1 ∧ p3))))) → p1) ∨ p5) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322331184456372707041864872616 : (p5 ∨ (((((True → ((p2 ∨ True) ∨ (p5 → True))) ∨ p2) → ((p2 ∨ ((p5 ∨ (p5 ∨ False)) → (p2 ∨ p4))) ∧ True)) ∨ (p4 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



