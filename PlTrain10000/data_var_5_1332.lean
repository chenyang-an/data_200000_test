variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665855464226230020450424915457 : ((((((p4 ∧ ((p2 ∧ (True ∧ ((p3 → p3) → p3))) → ((p3 ∧ (True ∧ p3)) ∧ p5))) → (p5 ∧ p3)) → False) ∧ ((p3 ∧ p2) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194820883865209857856015460284 : (((((p3 ∨ (p5 → p5)) ∨ p2) ∧ p4) → p4) ∧ ((p5 → (((p2 ∧ (((False → ((p1 → True) → False)) → p4) ∧ p4)) ∨ p1) ∨ p5)) ∨ False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15034210064315789868084285470 : (((True ∧ ((((p4 ∧ p2) ∧ p3) ∧ (p2 ∧ (False ∧ (False ∧ (p4 ∨ (p3 → (p3 ∧ (p5 ∨ (p5 ∨ True))))))))) ∧ True)) ∨ (p5 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_186035767983680566697053089009 : ((((((True ∨ False) ∧ p3) ∧ (p2 ∧ (p4 → p5))) ∧ p1) ∨ p3) → (p1 ∨ (((((True ∧ (p2 ∨ True)) ∧ p2) ∧ (p4 → p2)) ∨ p2) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h6.left
      let h11 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158683011082136613895086328204 : ((p2 ∧ ((((False → False) ∨ p1) ∧ (p3 → (p4 ∧ (p5 ∨ False)))) → ((p5 → (p5 → True)) ∧ p4))) ∨ ((p4 → (p1 ∧ p2)) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664934927366639170313615220776 : ((((p3 → ((((False → ((p2 ∨ True) ∨ (True ∧ p5))) → p2) → (True ∧ (False → p5))) ∧ ((p2 ∨ p2) ∧ (False ∧ p2)))) → (p3 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135965450108684248648918564564 : (((p4 ∨ ((p2 → p1) ∨ (((p5 ∨ p1) ∧ p2) ∧ p4))) ∧ ((((True ∨ p5) ∨ (p3 → (p1 ∨ p2))) ∧ p5) → p4)) ∨ ((False → p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631954093269361499459903781477 : (((((((p1 ∨ p5) ∧ False) ∧ (p3 ∧ ((False ∨ (p4 ∧ p4)) ∧ ((((True ∨ ((p4 → p3) ∨ p5)) ∧ p4) → p1) → False)))) → False) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172770687792923181289710836977 : (((p1 ∨ p4) → (((p4 → p1) ∧ (((p4 ∨ p1) ∧ True) → (p4 ∧ p1))) ∨ p2)) ∨ ((((p5 ∨ ((p5 ∧ p1) → True)) ∧ p3) ∧ False) → p4)) := by
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
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199266210839986730555808658175 : ((((((p1 ∧ p1) ∨ p4) ∨ p1) ∧ p1) ∨ True) → ((p3 ∧ ((True ∧ (True ∨ p3)) → ((p1 → False) ∨ (p4 → True)))) ∨ ((True → p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622356723729987097562050038482 : ((((p3 ∧ (((((p3 ∨ ((p4 → p5) ∧ p5)) ∧ p1) ∧ p5) ∨ ((p5 ∧ ((False ∨ p2) ∨ (p3 ∧ p1))) ∨ True)) → (p4 → p3))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_149109305654523425367930323321 : (((p4 → (p4 ∨ p2)) → (p2 ∧ ((p4 ∨ p5) ∧ (((p5 → p5) → (p1 ∨ ((p4 ∧ p3) ∨ p1))) ∧ p3)))) ∨ (((p5 ∧ False) ∧ False) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60835591713386081167068148142 : ((True ∧ (False ∨ ((p2 → (True ∧ p4)) → (((((((p1 → (False ∨ p2)) ∨ False) ∨ p4) ∨ True) ∨ (p3 ∨ True)) ∨ p3) ∧ (p3 → True))))) ∨ p3) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305674799873573804537445267840 : (p1 ∨ (((p5 ∧ ((True ∧ (p1 → True)) ∧ p4)) ∧ (p5 ∧ p2)) ∨ (p3 ∨ (p2 → (p2 → ((False → (True ∨ p3)) ∨ (p4 → (False ∨ True)))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56924564950783033383588836030 : (((True ∨ (False ∨ p2)) ∧ ((p2 → (False ∨ (p1 ∨ ((p3 ∨ p4) ∧ (True ∧ False))))) ∨ (p2 → (((p3 → False) ∧ False) ∨ (p1 ∨ True))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64431955798312098748230923255 : ((p1 ∨ ((True ∧ (((p3 ∧ ((p5 → p2) → (((p4 ∧ (p2 ∨ p4)) ∧ p5) ∨ (p1 ∧ p4)))) ∨ (p3 ∧ p5)) ∧ p4)) ∧ (False ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40549344000075169545466663445 : ((((True → ((p5 ∧ (True ∧ True)) → (((((False ∨ (p1 ∨ (p3 ∧ True))) ∨ (False → p2)) ∧ True) ∨ p4) → (p3 ∧ p4)))) ∨ True) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174207957664739680046866321197 : (((((p3 → p2) → ((p1 → False) → ((p1 → True) → p5))) → p4) → (p3 ∧ p2)) → ((p4 → (p2 ∨ p1)) ∨ (p4 ∧ (p1 → (p4 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 → p2) → ((p1 → False) → ((p1 → True) → p5))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311769117907489950675820472628 : (p2 ∨ (False ∨ ((p4 ∨ ((p2 → p4) ∨ (p5 → p5))) ∧ ((((p2 ∧ False) ∧ (((p4 ∧ p3) ∨ p2) ∧ False)) ∨ (False → p5)) ∨ (False ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692765107826813267098173042883 : (((((p5 ∧ ((True ∧ p4) ∧ False)) ∨ (((p2 ∨ p2) ∨ p1) ∨ (p2 → False))) ∧ (p3 ∧ (((p4 → p4) ∨ p5) → (p1 ∧ (True ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45420457626556818352322215594 : (((p5 ∧ (p2 → (False ∨ ((True ∨ (p2 ∧ p4)) ∧ (((p3 ∨ p1) ∨ ((False → ((p1 → p3) ∧ p1)) ∨ (p2 ∧ False))) → p3))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109408114878692528479375897305 : ((p2 ∨ ((((p5 ∨ ((p2 ∨ (p5 ∨ ((((p5 → True) ∨ True) ∧ (p3 ∨ p1)) ∨ p2))) ∨ (p5 ∨ p1))) ∨ p5) ∧ False) ∨ True)) ∧ (p2 → True)) := by
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
theorem thm_5_vars_49328213892271512418604687896 : (((p4 ∨ (p4 ∨ (((False → p3) → (((False ∨ True) → False) ∧ p3)) ∨ ((p3 → (p5 → (False ∧ p1))) → True)))) ∨ (p2 ∧ (p5 ∧ False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_192248688334170891063716332729 : ((((p1 ∨ ((True ∨ p3) ∨ False)) → (p1 ∧ p1)) ∧ p2) → ((p1 ∧ ((p2 ∧ p2) ∧ (p1 ∨ (p2 ∧ p5)))) ∨ ((p1 ∧ (p5 ∨ p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27844114598973929332874148351 : (((True → True) → ((p4 ∨ ((((False ∨ p5) ∧ ((p4 ∧ p3) → False)) ∧ (p4 ∧ p5)) ∧ (p2 ∧ ((p1 ∨ (True → True)) ∨ p5)))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_233465487621876352614047932105 : ((False ∨ (p4 → p3)) → (p4 ∨ ((p3 ∨ (p1 ∨ (((p3 ∨ p3) ∨ (p3 → p3)) ∧ ((p5 ∨ p3) ∨ ((p3 ∨ (p1 ∨ p3)) → True))))) ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151716624485378803430816774079 : (((((p1 → p2) ∧ (p1 ∨ False)) ∧ (((p2 ∧ False) → ((True ∨ p4) ∨ False)) ∨ False)) ∨ ((p5 ∧ p2) ∧ p1)) → ((p3 → p5) ∨ (p5 → p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38280567986419565302319501895 : (((((((True → (p1 ∧ p1)) ∧ False) → (False → p3)) ∧ (((p2 → True) → (p1 ∨ p4)) ∧ p3)) ∨ ((p2 ∨ p5) ∨ (p4 ∧ False))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356863905351514687783658431461 : (p5 → ((False ∧ (False → (p3 ∧ p2))) ∨ (((False ∨ (p4 ∨ True)) ∧ (((True ∧ False) ∧ True) ∨ (p5 ∧ p4))) ∨ (False → (True → (p1 ∧ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303837349300251433955261281284 : (p1 ∨ (((((((p3 → True) ∧ p1) ∨ (True ∨ (p3 ∨ p2))) ∧ ((p3 ∨ (p5 ∨ p1)) ∨ p1)) ∧ (p1 ∧ (p2 → p3))) ∨ (True ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_713792203320596849025814907789 : (((((((p1 ∧ True) ∧ p1) ∨ p3) ∨ p3) → ((p1 ∨ (p5 ∨ p1)) ∨ ((p5 → ((((p3 ∧ p1) ∨ p4) ∨ (True ∨ p5)) ∨ p5)) ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66839429968338541296851525696 : ((True → (p2 → (p1 → (True → (((p2 ∧ p2) → p2) → (((p4 → True) → p4) ∨ ((p2 ∨ (((False ∨ p5) → p2) → p3)) ∨ p2))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265742574579646794905430001322 : (True ∧ (p3 ∨ (True → (((p3 → (p1 → ((False → p3) ∧ (False ∨ ((((p1 ∧ p2) ∨ p4) ∧ p1) ∨ (p5 ∨ (p5 → p4))))))) ∨ p2) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779271501309235232086125880844 : (((p2 ∨ (((p4 → p1) ∨ ((True ∧ ((p4 ∨ p4) ∨ p2)) → ((p4 → p5) ∧ ((p4 ∧ (((p3 ∧ False) ∧ True) ∧ p2)) ∧ False)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697772440036552475451220963893 : ((((p3 → ((((p4 ∧ (p5 ∨ p1)) ∧ (p3 → p4)) ∨ p5) ∨ True)) ∧ ((False ∧ (((True ∧ p2) ∨ (True ∧ (p1 ∧ p2))) → p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153349581610500488962387637980 : ((p2 ∨ (((p1 ∨ p3) ∨ ((((p1 → (p1 ∨ p3)) → (False ∧ p5)) ∨ True) ∧ p1)) → (p3 → (True → p3)))) → (p5 ∨ (True ∨ (p2 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120997592232503273432090015919 : ((((p2 → p2) ∧ (((((p1 ∨ ((p4 ∧ (False → False)) → (False ∨ False))) ∨ (p5 ∨ p3)) → p4) ∧ p3) ∨ (False ∧ p5))) ∨ p1) → (p4 ∨ p1)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : ((p1 ∨ ((p4 ∧ (False → False)) → (False ∨ False))) ∨ (p5 ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158409616496706939424875345495 : (((p1 ∧ True) ∨ (((p2 → False) ∨ ((p1 ∧ True) → (p1 ∨ (((p1 ∧ p1) ∨ p1) → p4)))) → p5)) ∨ (True ∨ ((False ∨ p2) ∧ (p1 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56241303700288535505152713870 : (((True → ((p1 ∨ True) ∧ p1)) ∨ ((p4 ∧ (p3 ∧ (p4 ∧ ((p3 ∧ ((p3 ∨ p3) ∧ (True ∨ p3))) → p1)))) ∨ ((p1 → p1) → True))) ∨ p2) := by
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
theorem thm_5_vars_112761303348319509645490464972 : ((((((p4 → p5) ∨ ((False ∧ True) ∧ p2)) ∧ (p4 → True)) ∨ (((p5 → False) ∧ ((p3 ∨ p3) → (p5 ∨ False))) → p4)) → p3) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210403261900424447923405250805 : (((p2 ∨ (p4 ∧ p1)) ∨ True) ∧ (True ∧ (((False ∧ p2) ∧ p4) ∨ ((True ∨ ((True → ((p5 → p3) ∧ p4)) → (True ∨ p5))) ∨ (True → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136634048347049285889892849077 : ((((p5 ∨ p1) ∨ p2) → ((False → False) → ((True → (p1 ∧ ((p5 ∧ p2) → p4))) ∨ (False ∨ ((p3 → p3) ∨ p2))))) ∨ (p2 ∨ (p2 ∧ p4))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48944698917456876396513330659 : (((((False ∧ p1) ∨ (p5 ∧ (((p5 → (p1 → (p1 ∧ ((p3 ∨ p4) ∧ (p5 ∧ True))))) → p3) → True))) ∧ False) ∨ (p1 ∨ (p5 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330797281435487104550550902419 : (True → (p2 → (((p1 ∨ ((p5 → p2) → (p5 ∧ ((p1 ∧ p2) → (p2 ∧ p4))))) ∧ ((p4 → (p1 → p4)) → True)) ∨ ((p3 ∨ False) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167099051773651794810170514034 : (((((((p3 ∧ p5) ∧ (False ∧ p4)) → p2) → ((True ∨ False) ∨ p2)) ∨ (True → False)) ∨ p2) → (((p4 ∨ p1) ∧ (True → p5)) → (True ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h9 := h4 h8
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h12 := h10 h11
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h19
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h23 := h21 h22
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h26 := h4 h25
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59784601795260196935271682085 : (((p2 ∧ p1) → (((((False ∨ p2) ∨ p2) → (((p2 ∨ p2) → ((p2 → (p5 ∧ p3)) ∨ False)) → (p5 ∧ p3))) ∧ p1) → (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161778764645441794873022926706 : ((p4 ∨ (p4 ∧ ((((False → (p1 ∨ p1)) ∨ ((p4 ∨ p2) ∨ p2)) ∨ (False → p2)) → (p3 ∨ p2)))) → (p3 ∨ ((False ∧ p5) ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182735163047012612544997949348 : (((((p2 ∨ p5) ∧ p1) → p2) ∨ ((True ∨ p5) ∨ (False → True))) ∧ (((p4 ∧ p3) ∧ (False → p4)) ∨ (((p3 ∨ (False ∧ False)) ∨ p1) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357325013871181088110677215195 : (p5 → ((True → p1) ∨ ((True ∧ True) → (((p5 ∨ ((p1 ∨ ((p4 → False) → p5)) ∨ p1)) → False) ∨ (p1 → (p3 → (True ∨ (False ∧ p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762613574481464169848525176 : (((p2 ∧ p4) ∧ (True ∧ ((((((True → p2) → p2) ∧ p2) ∨ (p1 → False)) ∧ (p4 → True)) → ((p3 → (True → True)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119489060380411288074644658473 : ((p4 → (p2 ∨ (p2 ∨ ((p1 → (p4 ∧ p2)) → (((p5 ∨ False) ∧ (p1 ∧ (p4 ∨ p4))) ∧ (((p4 ∧ p2) ∨ False) ∧ p1)))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138038143906773836390000037731 : ((True → (((False → (p1 ∨ (p4 ∧ ((p4 → p4) ∧ p3)))) → p2) ∧ (((True → ((p1 → p2) ∨ p2)) ∨ p2) → p3))) ∨ (False → (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628094276073829350540862659454 : ((((((p5 → (p5 ∨ (p1 ∧ p5))) → (((((p2 → ((p4 ∨ p2) ∨ (p4 → p2))) → p4) ∨ True) ∧ p2) ∧ (p1 ∧ p1))) ∧ True) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805529964890807766817876915862 : (((p3 → (p4 ∨ (((p4 ∧ (True ∧ (p2 → p3))) ∧ p2) ∨ (((((p1 ∨ p2) → p4) → p4) ∨ (p3 ∨ (True ∧ (True → True)))) ∨ False)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790809112040841503028377101661 : (((p5 ∨ (p1 → ((((p5 → p1) ∨ p1) ∨ (p5 → p3)) → ((p5 → p2) → ((True ∧ (p3 ∧ (p4 ∨ (p2 ∨ (True ∧ p3))))) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199752336149705972935285197603 : (((p5 ∨ (False ∨ ((p2 → True) ∨ True))) → False) → (((False ∧ p2) ∧ ((p2 → p1) → True)) ∧ ((p4 → False) ∧ (p3 → ((p1 ∨ p3) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (False ∨ ((p2 → True) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (False ∨ ((p2 → True) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∨ (False ∨ ((p2 → True) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233552651000590107310868861576 : ((p1 ∨ (True → False)) → ((p2 → (p3 ∨ ((((p2 ∨ (False → p4)) ∨ (p1 ∧ ((p1 ∨ p4) ∧ True))) ∨ p4) → p3))) ∨ (p4 ∨ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729840812337481946333019603599 : (((((False ∧ p1) → p4) → (p4 ∨ (((p4 ∨ (p1 → True)) ∧ p3) ∨ (True ∨ ((((False → p3) ∧ p1) ∨ ((p3 ∧ False) ∨ p2)) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216315172902688308587854766666 : ((p2 → (p3 ∧ (p4 ∨ p5))) ∨ ((p2 ∧ p1) ∨ (((p4 ∧ ((p4 ∨ (p3 ∨ (p1 ∨ False))) ∨ (p2 → p2))) ∨ ((p3 ∧ p5) → p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211409569285482779446697374227 : (((p2 → p2) ∨ (p4 → True)) ∧ ((p3 ∧ ((((False → p3) ∨ (((p1 ∧ p4) → p3) → (p1 → (p4 ∨ p2)))) ∨ p2) → (p5 ∧ p4))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53537532292064913958437073831 : ((((((p4 ∨ False) ∧ (p3 ∨ (p5 → p5))) ∨ False) ∧ False) ∧ (p5 ∧ (True ∨ (p1 → ((p3 ∨ (p1 → (False ∨ (p3 ∨ False)))) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261072508138215922866511408937 : ((p4 → p3) → (((p5 ∨ (((p3 ∧ p3) ∨ ((p5 ∨ p5) → (p1 ∨ (False ∨ p4)))) → p1)) ∨ ((True ∧ True) → ((p3 → False) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258484443499623637298771021619 : ((p5 ∨ p2) → (((p4 ∧ p3) ∨ ((False → (True ∧ (p5 ∧ False))) ∧ p1)) → ((False → p5) → (((p4 → p3) → (p2 → (p5 → p3))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159327004954235771540344091145 : ((p5 → ((p3 ∧ p3) → ((p2 ∧ (p2 ∧ (((p2 ∧ p1) ∧ (p4 ∧ p4)) ∨ p2))) ∨ (p5 → p3)))) ∨ (p3 → ((p2 → (p5 → True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104572921146201741717567132672 : ((((((p4 → ((p5 → p4) ∧ p2)) ∧ p1) ∨ ((p1 ∨ (p5 ∨ p2)) ∨ (p5 ∧ p2))) → ((p4 ∧ p2) → False)) ∨ (True ∨ True)) ∧ (True → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_499581693149090413316159998804 : (((((p2 ∧ p1) ∨ p3) ∨ (((True → (((((False ∧ p2) ∧ p3) ∨ p2) → (p3 → ((False ∧ True) ∨ (p3 ∨ p3)))) ∧ False)) → p3) ∨ p3)) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50947278502168572645523591245 : ((((p1 → (((False ∧ (p2 ∧ p3)) ∧ p1) ∨ p1)) ∧ (p5 → ((p2 ∨ (p1 ∧ False)) ∧ p5))) ∧ (p1 ∨ (((p2 ∧ p5) → True) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721919488075058672618918277096 : ((((p5 ∨ (p1 ∧ (False ∨ p2))) → (((p4 ∨ (p1 ∨ ((False → True) → p3))) ∨ ((p2 ∧ (p2 ∧ True)) ∨ (True ∨ p4))) ∧ (False → p1))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639845143802089000752171770715 : ((((((True → p2) ∨ p5) ∨ (False → (True ∧ ((((p4 → (p1 → ((True ∧ p2) ∧ True))) → p5) → p3) ∨ (p5 ∧ (p1 ∨ p3)))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166273198493699169161402721409 : ((p3 ∧ (True → (p2 → (((((p5 ∧ (p1 ∧ p1)) ∧ p3) ∧ p1) → (p2 → p2)) → False)))) ∨ (p4 → (p2 → ((False → (p3 ∨ p5)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356714959622348451195935737891 : (p5 → ((((p2 ∨ True) ∨ (p1 ∧ p5)) ∧ p2) ∨ (p2 ∨ (((p5 → p2) ∧ (True ∧ ((True → (p4 ∨ p1)) ∧ (p3 → (p4 ∨ True))))) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793550056957235894543561988157 : (((True → (p2 ∨ ((p3 ∧ (p2 → (False ∧ p3))) → (((((((p2 ∨ p2) ∨ True) ∧ False) → p2) ∧ p5) ∨ ((p4 ∨ p1) ∧ p5)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113520270461313823283870088398 : ((((p4 ∧ ((p5 → (p4 ∧ (False ∧ p3))) ∧ (p2 ∨ False))) ∨ ((p2 ∨ True) ∧ ((False → (p3 ∧ False)) ∨ p3))) ∨ (p2 ∨ p1)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317639267198547880169986360840 : (p4 ∨ ((((p5 ∧ p4) ∨ (p1 ∨ (p5 → (False ∧ (p3 → (p5 ∨ (((p1 ∨ (p3 ∧ (p3 ∧ (True ∧ p3)))) ∨ p2) → p4))))))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62140423466468029298940447564 : ((p2 ∧ (p5 ∨ (p4 ∨ ((True → ((p4 ∨ (p5 ∨ p2)) ∨ p3)) ∧ ((True → ((p3 → p3) → (True ∧ (p3 ∧ True)))) ∧ (p4 ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751867707811301325150420581984 : (((True ∧ (p2 ∨ ((((p3 ∧ ((p5 ∨ p4) ∧ p2)) ∨ (True ∨ (((p1 → p4) → p3) ∧ p5))) ∧ (p4 ∨ (p5 ∧ (p3 ∧ False)))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356076970334626411350715606042 : (p5 → (((p1 ∧ (p1 ∨ (p2 ∧ (False → (False ∧ p2))))) ∧ ((p5 ∧ ((p5 ∧ (True → p5)) → False)) → p2)) → ((p2 → (p1 ∧ False)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319528504206168006546881419800 : (p4 ∨ ((p1 ∨ (True ∨ ((p4 ∧ (p4 ∧ (p5 ∧ p4))) → True))) ∧ (p5 ∨ (p2 → ((p4 → (p4 ∧ p2)) → ((p5 → p1) ∨ (p5 → p2))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679302113187135161741030756708 : ((((p1 → (p3 ∧ ((True → ((False ∧ (False ∨ p2)) ∧ p4)) ∨ ((p2 ∨ False) ∨ ((p5 ∨ True) → p5))))) ∨ (p5 → (True → (p5 ∨ False)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111862229414268573637369052081 : (((((p1 → (True ∨ p5)) → (((True → p4) ∧ (((False → p5) ∨ False) ∧ True)) → p3)) ∧ (p4 ∧ (p4 ∨ (p1 ∨ True)))) ∨ True) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677126801103619165310159131501 : ((((p5 → (((p1 → (p1 ∨ p5)) ∨ (p3 ∧ (p4 ∧ (False → p1)))) ∧ ((True → p3) ∧ (p5 ∧ p1)))) ∧ (p2 ∧ (False ∨ (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316369894790167689004906743456 : (p3 ∨ (False ∨ ((p5 → ((p3 → (((p3 ∧ False) ∧ ((p2 ∧ ((False → (p1 ∨ (p1 ∨ True))) ∧ (p4 ∨ True))) ∨ p2)) ∨ p3)) ∨ True)) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158763876080027229731260836789 : ((p4 ∧ ((p4 ∨ (p1 → p1)) → (p5 → ((p5 → (p3 → p1)) ∧ (((p3 ∧ False) → p4) → p2))))) ∨ ((p3 ∧ p5) → (p2 ∨ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158972450872598767854732275780 : ((p3 ∨ (((p5 → (p3 ∧ (((p2 ∧ p1) ∧ ((False ∧ (True ∨ p3)) → p1)) ∧ False))) ∧ True) → p1)) ∨ ((False → p1) ∨ ((True ∨ p5) ∨ p2))) := by
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
theorem thm_5_vars_668414731410769191955214055318 : (((((((((p3 ∧ (p2 ∨ ((p3 ∨ False) → p1))) ∨ p1) ∧ (False → p4)) ∧ ((p3 ∨ True) ∨ p5)) ∨ False) ∧ p3) ∨ ((True ∨ p5) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151026435442470854245267784200 : (((p5 → (p2 → (((p3 → p4) ∧ ((p3 ∨ p4) ∧ (((p4 → (p5 ∧ p1)) → True) → p4))) → False))) ∨ p2) → ((p1 ∧ False) ∨ (p4 → p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157200350849431059826671892100 : (((((p3 → ((p4 ∨ ((p5 → (p1 ∨ p3)) ∧ True)) ∨ False)) ∧ (True ∨ True)) ∨ (True → p5)) → p1) ∨ ((True ∧ p1) → ((p1 ∧ p1) ∨ True))) := by
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
theorem thm_5_vars_201000910766671085289522621393 : ((p3 ∨ ((p4 → True) ∧ ((p3 ∧ p5) ∧ p2))) → (((p4 ∧ p2) ∧ p4) ∨ (((p2 → p4) ∧ p1) → (p1 ∨ (p4 → ((p1 ∨ p5) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53767292340480775157709457234 : ((((((True ∧ p1) ∧ ((True ∨ p4) ∨ p5)) ∧ False) ∨ p4) ∨ ((p1 → (((False → p4) → p3) ∧ p4)) ∨ (p3 → (p2 ∧ (p2 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113149355476148923251537297258 : (((p3 → ((p3 ∧ (p1 ∨ p1)) ∨ (p4 ∧ ((False → (p2 ∨ False)) ∧ (((p5 → True) → False) ∨ ((False ∨ p1) ∧ p1)))))) → p5) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114249080683837792339902849141 : (((p5 ∨ ((((p3 ∨ p1) ∧ p1) → (p2 ∧ (p1 ∧ p1))) → ((((False ∨ p3) ∨ p4) ∨ p4) ∧ p3))) → ((p4 → p3) → False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319379036953906882895398810009 : (p4 ∨ ((p4 ∧ ((((p2 ∨ (p2 ∧ p3)) ∧ (p3 ∨ p4)) ∨ (False → False)) ∨ p3)) ∨ (((p4 ∨ (p4 ∧ False)) ∧ (p5 → (p5 → p1))) → p4))) := by
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
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_491167235082237844217719472659 : ((((((p4 ∨ p5) ∧ True) ∧ True) ∨ (((p1 ∧ p4) ∨ ((p2 ∧ (p3 ∧ (p1 → (p5 ∧ (p3 → ((p3 ∨ True) ∨ p2)))))) → False)) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_330793586650778432966745164356 : (True → (p2 → ((((p4 ∨ p3) ∧ (((p4 ∧ (p4 ∨ p2)) ∨ True) ∨ (True → p4))) ∨ ((((p2 ∨ p5) ∨ p2) ∧ False) ∧ p3)) ∨ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725981481640077866161435732850 : (((((p4 → p1) ∧ p1) ∨ ((((True → p5) → (((p3 → p4) ∧ p2) ∨ (p1 ∨ True))) ∧ (True → (p5 ∨ (p2 ∨ False)))) ∨ (p2 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118136147931796502726437071980 : ((False ∨ ((((False ∧ p3) ∧ (((((False ∨ p3) ∧ p3) ∧ p2) ∨ p2) ∧ p5)) ∧ (p2 → p2)) ∧ ((False ∧ p5) ∨ (p2 ∨ p5)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46585408250026036831178489919 : (((False ∧ (((p4 ∧ ((p5 ∨ p1) ∨ p5)) → p3) → ((p5 ∨ (((False → p5) ∧ (True ∨ (p5 ∨ p5))) → p2)) ∨ False))) ∧ (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117768698795708084854062382966 : ((p4 ∧ (((True ∧ (p3 → p1)) ∨ (p3 → ((((((False ∨ True) ∧ (False ∧ p1)) ∨ p4) ∨ True) ∨ False) ∨ p5))) ∧ (True ∨ True))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46861666993677953582360190910 : ((((p5 ∧ (((p1 → (p2 ∨ (((True ∧ (p5 → p2)) ∨ p2) → (p2 ∨ True)))) → (p5 ∨ p5)) ∧ (p2 ∧ p3))) ∧ True) ∨ (True ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627729071493606939196464452748 : (((((((p5 ∧ ((p2 ∧ (((p4 → True) ∨ (p3 ∨ p1)) ∨ p2)) → (p5 ∧ p3))) ∨ p5) ∧ (p1 ∨ ((p4 → p3) ∧ p3))) ∧ p2) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



