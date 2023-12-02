variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217850463869315345444152515900 : (((p5 ∨ (p5 → False)) → p1) → (((((False → True) → ((p2 ∨ p3) ∨ p3)) ∨ True) ∨ (False → (p1 ∨ False))) ∨ (((p4 ∧ p1) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949766196072061116360166446507 : (((((p2 → p3) ∨ False) ∧ (p2 ∧ (((((p3 ∨ p3) → p3) → (p2 ∨ (True → (False ∨ (False → (False ∧ p1)))))) → p5) → (False ∧ True)))) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352863500990576571083535828927 : (p4 → (True ∧ (((((p3 ∨ ((p4 → (((p1 → (True → p3)) → p1) ∨ (p3 ∨ (False ∧ (p2 ∨ p2))))) ∧ p5)) ∧ p5) → False) ∨ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133521101202133486603484563059 : ((((((p5 → p2) ∨ (p2 ∨ (p1 ∨ (p4 → ((p2 ∧ (p5 → p5)) → (p3 → (True → p3))))))) → p1) ∧ p5) ∧ True) ∨ ((True → False) → p1)) := by
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
theorem thm_5_vars_734339886496042574320670822788 : ((((False ∨ p3) ∧ ((((True → ((p2 ∧ (p5 ∧ (True ∧ p2))) ∧ (p5 → p3))) ∨ (p3 ∧ (p2 → (True ∧ False)))) → True) → (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305133117791901981337059292694 : (p1 ∨ (((((p2 ∧ p2) ∧ False) ∧ p4) ∨ (p5 → (True ∨ (((p3 ∨ (False ∧ p3)) ∧ True) ∨ (p2 → p4))))) ∧ ((False → (True ∨ p2)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114797315157309262890160629207 : ((((p4 ∨ ((p1 → (False ∧ (p4 ∧ True))) ∧ p2)) ∧ ((False ∧ p5) ∧ p2)) ∧ ((((p5 ∨ p4) ∨ p1) → (True → p4)) → p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142327965625083286915674379732 : ((p3 ∧ (((((p1 ∨ False) ∨ p2) → (p2 ∨ (((True → p5) ∨ True) ∧ False))) → (False ∨ (True ∨ p5))) → (p2 ∧ False))) → ((p5 → False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p1 ∨ False) ∨ p2) → (p2 ∨ (((True → p5) ∨ True) ∧ False))) → (False ∨ (True ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135017173028463991532766386748 : (((True → ((p2 → (((p4 → (p4 ∧ False)) → False) ∨ (((p1 ∨ p1) ∨ p4) ∧ (False → True)))) ∧ p2)) ∧ (p1 ∧ p3)) ∨ ((True → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354586459512794765923945329284 : (p5 → (((True ∧ (False ∨ ((p5 ∧ p3) ∨ ((((p4 ∨ (p3 ∧ True)) ∨ (p3 ∨ ((False → (p5 → p3)) ∨ p4))) ∨ False) ∨ p1)))) ∧ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134260060601001627197070803094 : ((((p4 → (p5 ∧ p5)) ∨ ((False ∨ (p3 → p4)) ∧ ((p1 ∨ p3) ∧ ((((p2 ∨ p5) → p5) ∨ p5) → p2)))) ∨ True) ∨ ((p4 ∨ p5) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158625781878961620109643198253 : ((False ∧ (False → (False ∧ (p5 ∨ ((p1 → (False → ((((p5 ∧ p5) ∨ p3) ∨ p1) → p3))) ∨ True))))) ∨ ((((False ∧ p1) ∧ False) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122799480690722281214592827944 : (((((p2 ∨ (p4 ∧ ((p5 ∧ (p2 → ((((False → p2) → p5) ∧ p2) ∨ p1))) ∨ p5))) ∨ p1) ∧ p3) ∧ (True → (p2 ∧ p3))) → (p2 ∧ p2)) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h19 := h3 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h21 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h23 := h3 h22
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- One of the premise coincides with the conclusion.
    exact h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h38 := h26 h37
        -- We need to get the left conjuct of h38 based on <expert-advice>.
        let h39 := h38.left
        -- One of the premise coincides with the conclusion.
        exact h39
      case inr h40 =>
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h41 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h42 := h26 h41
        -- We need to get the left conjuct of h42 based on <expert-advice>.
        let h43 := h42.left
        -- One of the premise coincides with the conclusion.
        exact h43
  case inr h44 =>
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h45 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h46 := h26 h45
    -- We need to get the left conjuct of h46 based on <expert-advice>.
    let h47 := h46.left
    -- One of the premise coincides with the conclusion.
    exact h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340896538773270668400327720542 : (p2 → (((((p4 ∨ True) → (True ∨ p5)) ∧ (p4 → ((p1 ∧ True) ∧ p5))) ∨ ((((True ∧ (p2 ∨ p3)) → p2) → (p5 ∧ p1)) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201178844118181885077422023616 : ((p1 → (((p4 ∧ p2) → (p2 ∧ p2)) → p2)) → ((((p5 ∧ ((p3 ∧ p4) → (p4 ∧ (p2 ∧ p2)))) ∧ ((True → p1) ∧ p1)) → p2) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : ((p4 ∧ p2) → (p2 ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h12.left
    let h16 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h17 := h10 h11
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355576243425529579059803249509 : (p5 → (((p2 → ((False ∨ ((p2 ∧ False) ∧ p3)) ∨ (p1 ∧ (p1 → ((p2 ∨ False) ∧ p1))))) ∨ ((p1 → (p3 → p3)) → p5)) ∨ (p2 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694632626146124009814346165534 : ((((p5 ∧ (p4 ∨ (((p1 → False) → p3) → ((p3 ∧ p4) ∨ (p2 ∨ p1))))) ∨ (p3 ∧ (((True ∨ p3) ∨ ((False → p5) ∨ p3)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64361904263301203904762065761 : ((p1 ∨ (((((True ∨ True) ∧ (p4 → True)) → (((p3 ∧ (False ∨ True)) ∧ p1) ∨ (p3 ∨ p4))) ∨ (False ∧ (p3 ∨ (True ∨ p4)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321122458662783640993737400607 : (p4 ∨ (p2 ∨ (((False ∨ (p3 → ((False ∨ True) → (p3 ∧ p3)))) ∧ (p5 → ((((p3 → p2) → (p3 → p4)) → p2) ∨ True))) ∨ (p4 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40197841013279902123568008913 : (((((p1 → (p1 → p3)) → (False ∧ (((((p3 → p4) ∧ (p1 ∧ True)) ∧ (p3 ∧ (p1 → p5))) ∧ p1) ∨ (p2 ∨ True)))) ∧ p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60477770492123197909390900723 : (((p5 → p5) → ((p5 ∧ (p1 ∨ p3)) ∧ ((True ∨ ((p4 ∧ (p2 ∧ p4)) ∧ ((p3 ∧ (p3 ∨ p3)) ∧ (p3 → (False ∨ False))))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338247090130929639008508416770 : (p1 → ((p2 ∧ (p3 → ((p5 ∨ p4) ∨ p2))) ∨ (((p1 ∧ p4) ∧ (((True ∨ (p5 ∨ False)) → p4) ∧ True)) ∨ ((p5 → (p4 ∧ p1)) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314451247015326302295396794693 : (p3 ∨ ((((((p5 ∨ p3) ∨ p1) ∧ (((p1 ∧ (p1 → (p1 ∨ False))) ∨ False) → (False ∨ p3))) ∧ p3) ∨ p4) → (p2 → ((p2 → p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323889449743968461492137261038 : (p5 ∨ (((False ∧ (False ∨ (p4 ∧ (((p3 ∧ (False → (p5 ∧ False))) ∧ False) → True)))) ∨ False) ∨ (False ∨ ((p2 ∧ False) → (p4 ∨ (p2 → p5)))))) := by
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
theorem thm_5_vars_185212131573885721124500798207 : ((True ∧ (p5 ∨ (((p2 ∧ p3) ∧ False) ∨ ((p3 → p5) → p5)))) ∨ (True ∨ ((False ∨ (p2 ∨ (p2 ∨ (p5 ∧ False)))) → (True ∨ (False → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57732215263290039257616960885 : ((((p3 ∨ True) → p1) → (p2 ∧ (((p5 ∧ (((False ∧ (p3 → p4)) → p3) → p4)) ∧ p5) ∧ ((p1 → (p4 → p1)) ∨ (p1 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28179878613369481825990361877 : ((True ∧ ((((((False ∧ p3) ∨ p2) → True) ∨ True) → (((p5 ∧ (((p5 → (p1 → (p5 ∧ p5))) ∧ True) ∧ p3)) ∨ p4) ∨ True)) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705802785367006173654631187308 : ((((((p4 ∨ False) → (p5 ∧ True)) → (p5 ∧ p3)) ∧ (((p2 ∨ (p3 → p5)) → (p1 ∨ p5)) ∧ (p4 ∨ ((p3 ∧ (p3 ∨ p2)) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113981548521586409535741259882 : (((p2 ∨ ((p4 ∨ (p3 ∧ (((p4 → False) ∨ p3) ∧ (True → ((p1 → (p2 → p5)) ∧ p5))))) ∨ False)) ∧ ((p3 → p4) ∨ True)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228441361156816667470157770634 : ((False ∨ (False ∨ False)) ∨ ((p3 → ((p5 ∨ True) ∧ (False ∨ True))) ∧ (True ∨ (p4 → ((p4 → (p3 ∨ p1)) ∨ (p5 ∧ (p1 ∨ (p5 → p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58927190316135091625304366849 : (((p1 ∧ p2) ∨ (p2 ∨ (((((p1 ∧ ((((False ∧ (p2 → p3)) ∧ (p3 → p1)) → p4) ∧ p5)) → (p5 ∨ p1)) ∧ p5) ∧ False) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342490764580229334002017979113 : (p2 → (((p4 ∨ p1) ∨ (((p3 → ((False ∨ p1) → p4)) → (p5 → False)) ∨ p2)) ∨ (p3 ∨ ((True → ((p1 ∧ (True → p5)) ∧ p1)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156818478180432813376334686948 : (((p3 ∨ ((p5 ∨ (p2 → (p5 ∨ (p2 ∨ (p2 → (p2 → False)))))) ∧ (p3 ∨ (p1 → p4)))) ∧ p3) ∨ (True ∨ ((p1 ∨ p1) ∨ (p5 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240448706293837849848771837362 : ((p5 ∨ True) ∧ ((False ∨ (((p1 ∨ (p5 ∧ p1)) ∨ p4) ∨ p3)) ∨ ((p5 ∧ (p3 ∨ (True ∧ p4))) → ((p2 → (p1 → False)) ∨ (False → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304693942506933623861289791014 : (p1 ∨ (((p2 → ((((p4 ∨ (True ∧ p2)) ∨ ((p4 ∧ ((p4 → p3) ∧ (True → (True ∨ p1)))) ∧ p3)) ∨ False) → p1)) ∨ p4) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136356864443163955660731909345 : (((((False → p4) ∧ p2) ∧ p4) ∨ (((((p2 ∧ (False ∧ ((p4 ∧ p3) ∧ p1))) ∨ (p2 ∧ False)) → p3) ∧ p2) → p4)) ∨ ((p4 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804025913696153024598538706876 : (((p3 → ((p2 ∨ (((((p5 ∧ (p1 ∧ (True ∨ p4))) ∧ True) ∧ p1) ∧ ((p5 ∨ p2) ∧ True)) ∨ (False → True))) ∨ ((p5 ∧ p4) ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326862040718195298500827251466 : (True → ((((p5 ∨ ((((p4 ∨ p4) ∧ p2) ∨ (p4 ∨ (((p2 ∨ p1) ∨ (False ∧ (False ∨ (p1 ∧ p2)))) → p5))) ∧ p2)) ∧ p2) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249490188200588065394754157464 : ((p5 ∨ p1) ∨ ((((p5 → (True ∧ (p2 → False))) → p4) ∨ ((p5 ∧ ((p4 ∨ (p4 → p1)) ∨ p3)) ∧ True)) ∨ (((True → p2) ∧ False) → p4))) := by
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
theorem thm_5_vars_4467589530158227240802125668 : (p2 → (((True ∨ (p4 → p1)) ∨ ((True → (False ∨ (p1 ∨ (((p5 ∨ p1) ∨ p4) → p2)))) ∨ True)) → (p4 → ((False ∧ p3) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300156672148248884262683726117 : (False ∨ ((True → ((((True ∨ (((p5 ∧ p5) → p3) ∧ (p4 → (p1 ∨ p1)))) → (p4 ∨ (False → p4))) ∧ (p4 ∧ p5)) ∨ True)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204871364960172041357934990926 : ((((p5 ∧ (p1 ∨ p2)) → p2) → False) ∨ ((p4 ∨ (((p3 → p2) ∨ ((((p1 ∧ True) ∧ p3) ∧ (p5 → True)) ∧ p1)) ∨ False)) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714228849823810784384249691930 : ((((((False ∧ p2) → p4) ∧ (True ∧ p3)) → (((((p1 → (p1 → p4)) ∧ (p2 ∧ ((p3 → p1) → False))) ∨ p3) ∨ p5) ∨ (True ∨ True))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252555315218497885695495515258 : ((p5 → p2) ∨ (p4 ∨ (((((True ∧ (p2 ∧ p4)) → False) ∧ p3) ∨ ((p5 ∨ p2) ∨ (p2 → p4))) → ((p1 ∨ (True ∨ (p5 ∧ True))) ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184646339057498123288437724396 : ((((False ∧ (p4 ∨ (False ∨ False))) ∧ p2) ∨ (False → (p4 ∨ False))) ∨ (p4 ∧ ((((p5 → (p2 ∨ (p3 → (p2 ∨ p1)))) ∧ p3) ∧ p4) ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238084507636064785865139417622 : ((True ∨ p2) ∧ (((False → p3) ∨ p4) ∧ (((p1 ∧ ((p4 ∧ ((p1 ∨ p3) ∧ p4)) → (p4 ∨ (p3 ∨ False)))) → (p5 ∧ False)) ∨ (False → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321276653790377457062167871644 : (p4 ∨ (p4 ∨ (p2 ∨ ((((((False ∨ p1) ∨ (((True ∧ False) ∧ (True ∧ (p5 ∧ p3))) ∨ True)) → p2) ∨ ((True → p4) ∨ True)) ∨ p3) ∨ False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171866975235501948928734581092 : (((p1 ∧ (((p3 ∨ p4) → p2) ∧ ((p1 → ((p5 ∨ p1) ∧ p1)) ∨ p1))) → p5) ∨ (False → ((p1 ∨ (True → False)) ∧ (p3 ∧ (p3 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252603914423654168842430091860 : ((p5 → p3) ∨ ((p5 ∨ p3) ∨ (p4 ∨ ((p4 → ((p3 → (p4 ∧ p5)) → False)) → ((((p3 ∧ p4) ∨ (False → p1)) ∧ (False ∨ p3)) → p3))))) := by
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
    cases h4
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178109330674117357061495611389 : ((((p1 ∨ (p4 ∨ ((p2 ∧ (p5 → p3)) → False))) ∨ (p5 ∨ True)) → p2) ∨ ((False ∨ (((p2 ∧ p1) → (p3 → (p3 ∨ True))) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_137116102693971015721847803244 : ((True ∧ (((p3 → p4) → (p1 ∧ (p2 → False))) ∧ (False ∧ ((p1 ∨ p2) ∨ ((p3 ∧ ((p3 ∧ p2) → p2)) ∧ True))))) ∨ ((p2 ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40758661589713296946059992088 : (((((p4 ∧ p5) ∨ (p5 ∨ ((p1 → ((p5 ∧ False) → ((False → ((p5 ∧ p5) ∨ True)) ∧ p3))) ∧ ((False ∧ p1) → p3)))) → False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664321488486408799048477849080 : ((((p2 ∨ (((((True ∧ p3) ∨ (p2 ∨ (p3 ∧ (p2 ∨ p1)))) ∧ False) ∧ p2) → ((p2 ∧ p5) → ((p3 ∨ True) → p5)))) → (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200092584381639158009460123565 : ((((p3 ∧ p3) → p4) ∧ (p4 ∨ (p3 ∨ p2))) → ((p1 ∧ (p1 ∧ p4)) ∨ (p2 → (((False → False) → (False ∧ ((p3 ∨ True) ∧ p3))) → p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148165876885105166316070864862 : (((((True ∧ p4) → (((p5 → (False ∨ (p5 ∧ p1))) ∨ True) → (p3 → p1))) ∧ True) ∧ (p5 ∨ (p5 ∨ p1))) ∨ ((p3 ∨ (False ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344687023782613708663205768027 : (p2 → (p2 → ((False → p3) → (p2 → (((((False ∧ p2) ∨ p4) ∨ (p2 ∧ ((False → False) ∨ p1))) → p4) → (((p3 ∨ p2) ∨ True) ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((False ∧ p2) ∨ p4) ∨ (p2 ∧ ((False → False) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715923538889496763137129479256 : (((((p4 ∨ (p5 ∧ p5)) ∨ True) ∧ (p4 → ((p5 → False) ∧ ((p5 → ((((p3 → True) ∧ p3) ∧ (True → p1)) ∧ False)) ∧ (p1 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174660650417442241684385682348 : ((((p5 → p2) → p4) ∧ (p3 ∧ ((((p1 → p2) ∧ p1) → True) ∧ (True ∨ False)))) → ((p3 ∧ ((p1 ∧ p2) ∧ p5)) ∨ ((False → p4) → True))) := by
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
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171935965956197664124818179760 : (((((p4 → (p4 → (p2 ∧ (p5 ∧ (p3 → p5))))) ∧ True) → p4) ∧ (p4 → p1)) ∨ (((p4 ∧ p3) ∨ p3) ∨ (p3 ∨ (False ∨ (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622975002407454152874437266933 : ((((p5 ∧ (((p3 → p3) ∧ (p1 ∧ p4)) → ((((p3 ∧ True) ∧ True) ∧ ((p1 → False) ∨ False)) ∨ ((False ∧ (p5 → True)) → p2)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757126895211878124370677959593 : (((p1 ∧ (((p5 → True) → p2) ∨ (p5 → ((p1 → ((p1 ∧ p4) ∨ p3)) ∨ ((((p5 → p1) ∨ p3) ∧ ((p3 ∨ p2) ∨ False)) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654495436775338837987062550810 : (((((True ∧ (False ∨ ((p3 ∧ ((p1 → (True ∨ True)) → (((p4 → p1) ∧ p2) ∧ (p3 ∧ (p3 ∧ p2))))) ∨ p2))) ∨ p3) ∨ (p1 → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_746915581258138387966712633953 : ((((p4 ∨ False) → (False ∨ (((False ∨ (p2 ∨ (p4 ∧ (((p5 ∨ p1) → (p5 → p1)) ∧ True)))) ∨ (p4 → (False ∨ (True → p4)))) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597506368868140382235748701552 : (((((p3 ∧ ((p5 ∨ p3) → True)) ∨ ((True ∧ p1) → (((((p1 → p4) ∧ (p4 ∨ ((p1 ∧ p5) ∧ True))) → p1) → p3) ∧ p3))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159415484208886051766542917595 : (((((((p3 ∨ (p5 → p1)) ∨ p5) ∧ ((p1 → (p3 ∧ p2)) ∨ p5)) ∨ p2) ∧ (True → False)) ∧ p5) → (p3 ∧ ((p5 → (p1 ∧ False)) ∧ p5))) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h14 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h16 := h5 h15
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h18 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h19 := h5 h18
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h21 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h23 := h5 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h26 := h5 h25
        -- False on the left can always be used.
        apply False.elim h26
  case inr h27 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h29 := h5 h28
    -- False on the left can always be used.
    apply False.elim h29
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h30
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h40 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h41 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h42 := h34 h41
          -- False on the left can always be used.
          apply False.elim h42
        case inr h43 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h44 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h45 := h34 h44
          -- False on the left can always be used.
          apply False.elim h45
      case inr h46 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h47 =>
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h48 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h49 := h46 h48
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h50 =>
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h51 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h52 := h46 h51
          -- One of the premise coincides with the conclusion.
          exact h52
    case inr h53 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h54 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h55 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h56 := h34 h55
        -- False on the left can always be used.
        apply False.elim h56
      case inr h57 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h58 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h59 := h34 h58
        -- False on the left can always be used.
        apply False.elim h59
  case inr h60 =>
    -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
    have h61 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h34, we can now drive its conclusion.
    let h62 := h34 h61
    -- False on the left can always be used.
    apply False.elim h62
  -- Conjunctions on the left can always be decomposed.
  let h63 := h1.left
  let h64 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h65 := h63.left
  let h66 := h63.right
  -- Disjunctions on the left can always be decomposed.
  cases h65
  case inl h67 =>
    -- Conjunctions on the left can always be decomposed.
    let h68 := h67.left
    let h69 := h67.right
    -- Disjunctions on the left can always be decomposed.
    cases h68
    case inl h70 =>
      -- Disjunctions on the left can always be decomposed.
      cases h70
      case inl h71 =>
        -- Disjunctions on the left can always be decomposed.
        cases h69
        case inl h72 =>
          -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
          have h73 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h66, we can now drive its conclusion.
          let h74 := h66 h73
          -- False on the left can always be used.
          apply False.elim h74
        case inr h75 =>
          -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
          have h76 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h66, we can now drive its conclusion.
          let h77 := h66 h76
          -- False on the left can always be used.
          apply False.elim h77
      case inr h78 =>
        -- Disjunctions on the left can always be decomposed.
        cases h69
        case inl h79 =>
          -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
          have h80 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h66, we can now drive its conclusion.
          let h81 := h66 h80
          -- False on the left can always be used.
          apply False.elim h81
        case inr h82 =>
          -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
          have h83 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h66, we can now drive its conclusion.
          let h84 := h66 h83
          -- False on the left can always be used.
          apply False.elim h84
    case inr h85 =>
      -- Disjunctions on the left can always be decomposed.
      cases h69
      case inl h86 =>
        -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
        have h87 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h66, we can now drive its conclusion.
        let h88 := h66 h87
        -- False on the left can always be used.
        apply False.elim h88
      case inr h89 =>
        -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
        have h90 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h66, we can now drive its conclusion.
        let h91 := h66 h90
        -- False on the left can always be used.
        apply False.elim h91
  case inr h92 =>
    -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
    have h93 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h66, we can now drive its conclusion.
    let h94 := h66 h93
    -- False on the left can always be used.
    apply False.elim h94
  -- Conjunctions on the left can always be decomposed.
  let h95 := h1.left
  let h96 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h97 := h95.left
  let h98 := h95.right
  -- Disjunctions on the left can always be decomposed.
  cases h97
  case inl h99 =>
    -- Conjunctions on the left can always be decomposed.
    let h100 := h99.left
    let h101 := h99.right
    -- Disjunctions on the left can always be decomposed.
    cases h100
    case inl h102 =>
      -- Disjunctions on the left can always be decomposed.
      cases h102
      case inl h103 =>
        -- Disjunctions on the left can always be decomposed.
        cases h101
        case inl h104 =>
          -- One of the premise coincides with the conclusion.
          exact h96
        case inr h105 =>
          -- One of the premise coincides with the conclusion.
          exact h96
      case inr h106 =>
        -- Disjunctions on the left can always be decomposed.
        cases h101
        case inl h107 =>
          -- One of the premise coincides with the conclusion.
          exact h96
        case inr h108 =>
          -- One of the premise coincides with the conclusion.
          exact h96
    case inr h109 =>
      -- Disjunctions on the left can always be decomposed.
      cases h101
      case inl h110 =>
        -- One of the premise coincides with the conclusion.
        exact h96
      case inr h111 =>
        -- One of the premise coincides with the conclusion.
        exact h96
  case inr h112 =>
    -- One of the premise coincides with the conclusion.
    exact h96



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319161375148456616674275114556 : (p4 ∨ (((((((False → (p5 ∨ p3)) ∨ (p5 → p3)) → (False ∨ p5)) ∧ (p3 → True)) ∨ p3) → False) ∨ ((False → (p3 ∨ p5)) ∨ (p5 ∧ True)))) := by
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
theorem thm_5_vars_156635165701629052699641412257 : ((((False ∧ (p4 ∧ (False ∧ ((False ∨ p1) ∨ (((p3 → (p2 → p4)) ∨ p1) → True))))) ∨ True) ∧ False) ∨ (((p1 → p5) → True) ∧ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615667007202017254860431462260 : ((((((False → (((p3 ∨ ((True ∨ p5) ∧ p2)) → True) ∨ (p4 ∧ p5))) → p1) ∧ (((p3 ∨ ((p4 ∨ True) → p5)) ∨ False) ∧ p5)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317656442547283962887183732033 : (p4 ∨ (((((((((p3 ∨ p4) → p3) ∧ (p4 ∧ True)) ∧ (p3 → ((p4 → ((p2 → p1) ∨ p4)) ∨ p5))) ∨ p3) → p4) ∨ p1) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121324454916838845073020365187 : ((((((p2 ∧ p1) ∨ p5) → (True → ((p2 → (False ∧ p2)) ∨ (p2 ∧ (p2 ∨ ((p1 → p3) ∧ (p4 → False))))))) ∧ p5) → p5) → (p3 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427291864819504528943937269649 : ((((((p3 ∧ ((((p2 ∧ p3) ∨ (p1 ∧ p1)) → p2) → p1)) ∧ ((p1 ∨ True) → ((p1 ∧ (p2 ∨ p2)) → p2))) ∧ p3) ∨ (False → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191258864098139092451927003156 : (((p4 ∧ p2) ∧ ((p4 ∨ (p1 ∨ p5)) ∧ (p2 ∨ p3))) ∨ (((p4 → p5) → p1) ∨ ((p2 ∨ ((p5 → ((p3 ∧ p1) ∨ p5)) ∨ p1)) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191926828049820738016502602017 : ((True → ((p2 ∧ ((p4 ∧ (p2 ∧ p5)) ∧ p2)) ∨ p3)) ∨ (p1 → ((((True ∨ p2) ∧ p2) ∧ False) ∨ ((p4 ∨ False) → ((p4 ∨ p1) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323670119096311195752526504177 : (p5 ∨ (((((p4 ∨ (p5 → p4)) ∨ True) → False) ∧ (p2 → ((((p2 ∨ p2) ∧ p1) ∨ (p3 → True)) ∧ p1))) ∨ ((p2 → p2) ∨ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338719109775636440056694178583 : (p1 → ((False → False) ∧ ((((((((p1 ∨ p2) ∧ False) ∨ p2) ∨ p3) ∧ True) ∨ (p1 ∨ (p3 ∨ p1))) → (True ∧ (False ∨ (True ∨ False)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114626834074047340056972643476 : ((((((((True → True) ∨ ((False ∧ (False ∨ p3)) ∨ p4)) ∨ False) → False) ∨ p1) ∨ p4) ∨ (p5 ∨ (True ∨ ((True → p5) ∧ False)))) ∨ (p2 → p2)) := by
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
theorem thm_5_vars_593132432822181982484981603692 : ((((((((p1 ∧ (True ∨ p1)) ∧ (p2 ∧ (p3 ∨ False))) ∧ (p5 → True)) → (((p2 ∨ True) ∧ p4) ∨ False)) ∨ (True ∨ (p4 → p4))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42051899576443678321414041068 : ((((p1 ∨ p3) ∨ (((((p3 ∧ True) ∧ p4) ∧ (True → ((p3 ∨ p4) ∨ p1))) → ((p4 ∧ p1) ∧ True)) ∨ (p4 ∨ (True ∨ True)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59492154567255888251698479297 : (((p1 → p5) ∨ ((p1 ∧ (p3 → ((((True ∧ False) ∧ True) ∧ (p1 → p4)) ∧ (((p4 → False) ∨ (p2 ∨ p3)) → p1)))) ∨ (p4 → True))) ∨ False) := by
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
theorem thm_5_vars_184828510532884035828541330117 : ((((True ∨ p3) ∧ (p3 ∨ p4)) → ((p3 ∨ p2) → (False ∨ True))) ∨ (((p3 → p1) ∨ p3) ∨ (p5 ∧ ((p1 → (p4 ∨ p1)) → (p1 ∨ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1615559373275906076189798088 : (((((False ∨ True) ∨ (((((p3 ∨ p1) ∧ p5) ∨ p3) ∧ (True ∨ p2)) ∨ (False ∨ p2))) ∧ p5) ∧ ((False ∧ p5) ∨ p4)) → (p1 ∨ True)) := by
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
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h22 =>
              -- Conjunctions on the left can always be decomposed.
              let h23 := h22.left
              let h24 := h22.right
              -- False on the left can always be used.
              apply False.elim h23
            case inr h25 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h27 =>
              -- Conjunctions on the left can always be decomposed.
              let h28 := h27.left
              let h29 := h27.right
              -- False on the left can always be used.
              apply False.elim h28
            case inr h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h32 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h33 =>
              -- Conjunctions on the left can always be decomposed.
              let h34 := h33.left
              let h35 := h33.right
              -- False on the left can always be used.
              apply False.elim h34
            case inr h36 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h31
          case inr h37 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h38 =>
              -- Conjunctions on the left can always be decomposed.
              let h39 := h38.left
              let h40 := h38.right
              -- False on the left can always be used.
              apply False.elim h39
            case inr h41 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h31
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h44 =>
            -- Conjunctions on the left can always be decomposed.
            let h45 := h44.left
            let h46 := h44.right
            -- False on the left can always be used.
            apply False.elim h45
          case inr h47 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h48 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h49 =>
            -- Conjunctions on the left can always be decomposed.
            let h50 := h49.left
            let h51 := h49.right
            -- False on the left can always be used.
            apply False.elim h50
          case inr h52 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h53 =>
      -- Disjunctions on the left can always be decomposed.
      cases h53
      case inl h54 =>
        -- False on the left can always be used.
        apply False.elim h54
      case inr h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h56 =>
          -- Conjunctions on the left can always be decomposed.
          let h57 := h56.left
          let h58 := h56.right
          -- False on the left can always be used.
          apply False.elim h57
        case inr h59 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215550623259804354189183070058 : ((p5 ∧ ((p5 ∧ True) ∧ p2)) ∨ (False ∨ ((((((p1 → (False ∧ p1)) ∨ (p1 ∨ p4)) ∨ p2) → False) ∨ (p5 → p2)) ∨ ((True ∨ p2) → True)))) := by
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
theorem thm_5_vars_118249262569551692914596582413 : ((p1 ∨ (((((p4 → False) ∨ p3) ∨ ((False ∨ p5) → (p4 ∨ False))) ∧ (((p4 → False) ∨ p1) ∧ p5)) ∧ (p5 ∨ (p4 ∨ p4)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150334030920838986011468227649 : ((p5 → ((p1 ∨ ((((p3 ∧ p5) ∧ (((p2 ∨ p1) ∧ False) → False)) ∨ ((p4 ∧ p3) → p2)) → p2)) ∨ p5)) ∨ ((p2 ∧ (p2 → False)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197053202977795059896415967299 : ((((p4 ∧ p3) ∨ (p1 ∨ (p5 ∧ p5))) ∨ True) ∨ ((p1 → True) ∨ ((p1 ∨ (((False ∨ p4) ∨ (p1 ∨ p3)) ∧ p3)) → ((False ∧ False) ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330508845361679740579610426390 : (True → (p4 ∨ ((p4 ∨ (p3 → p4)) ∨ ((False ∨ ((((p1 → True) → (False ∨ (p4 → True))) ∨ True) ∨ p5)) ∧ (((False ∧ True) ∨ False) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120928101732628632044563726855 : (((((False → p4) ∧ (p5 → p2)) ∨ ((True → p5) ∨ ((((((p3 ∧ (p4 → False)) ∧ p2) ∧ p1) ∨ p4) ∨ p1) ∨ p5))) ∨ True) → (p4 → p4)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Conjunctions on the left can always be decomposed.
              let h13 := h12.left
              let h14 := h12.right
              -- Conjunctions on the left can always be decomposed.
              let h15 := h13.left
              let h16 := h13.right
              -- Conjunctions on the left can always be decomposed.
              let h17 := h15.left
              let h18 := h15.right
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h19 =>
              -- One of the premise coincides with the conclusion.
              exact h19
          case inr h20 =>
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h2
  case inr h22 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785452866180782176394293935750 : (((p4 ∨ (((p3 ∧ ((p4 → p1) → (True → (p2 ∨ p4)))) ∨ (True ∧ (((((p2 ∧ False) ∧ p5) ∧ False) → (p5 → p5)) → True))) ∨ p3)) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158520473408430007860183207754 : (((p3 ∨ p4) → (((((True → p4) ∨ p3) ∨ True) ∨ (p4 ∨ (p1 ∧ False))) → ((p3 ∨ False) ∧ p2))) ∨ ((False ∨ (True ∧ (True ∧ True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190116594623105300164019681269 : (((((p1 → p2) ∧ False) ∨ (True ∧ (p5 → p1))) ∧ p4) ∨ (p3 ∨ (p4 ∨ ((((False → ((False → p2) ∧ p4)) ∨ p3) ∨ (p2 ∨ p4)) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190370731853943952114762463935 : ((((p2 ∨ p1) ∨ (((p5 ∨ p4) ∨ p1) ∨ p5)) ∨ False) ∨ (True ∧ (((((True ∨ p1) ∨ p5) → p3) → (p3 ∨ p1)) ∨ ((p3 → p2) → p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p1) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48207096952208296718233583637 : ((((True ∨ True) → ((p5 ∧ p3) ∨ (((p4 ∧ (True → ((((p1 → False) ∨ p3) ∨ (False ∧ p2)) ∧ True))) ∨ True) → p2))) → (p4 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314781319777610186851287106777 : (p3 ∨ (((p5 ∧ p4) ∧ ((True ∨ p4) ∨ (((p4 → p4) ∨ (p5 ∨ p5)) ∧ p3))) → (((p5 ∧ p2) ∧ ((p3 → (p3 ∧ p1)) → p2)) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70598850562493868034532380157 : (((((True → (((False ∧ True) ∧ p4) ∧ (((p5 ∧ True) ∨ (p2 ∨ (p3 ∨ p4))) ∨ p2))) ∧ p1) ∧ (p4 ∨ (p2 → (p3 → p1)))) ∧ p3) → False) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109296519034832699831919664552 : ((p1 ∨ ((((p1 ∧ p4) ∧ p2) ∨ ((p4 ∨ (p1 → (((p5 → p3) ∧ (p3 ∨ (False ∨ p1))) ∨ (p5 ∨ p1)))) ∨ False)) ∨ p4)) ∧ (p3 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780086363681390961560527996792 : (((p2 ∨ (((((p3 ∧ True) ∧ (p5 ∨ (((p2 ∨ p5) ∨ (True ∨ (p1 ∨ True))) ∧ True))) ∧ (p4 ∨ p4)) ∨ (p2 → p4)) → (p5 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67451919743815257924892734003 : ((p1 → (((p2 ∨ (p5 ∨ ((((p5 ∨ False) ∨ (p3 ∧ p4)) ∨ ((True → True) → p1)) ∨ p5))) ∧ False) ∧ ((p1 → p3) ∧ (True ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260172002629101408820397550237 : ((p2 → p2) → (((((p4 ∧ p5) → (((((p4 ∨ p3) ∨ ((p3 → p1) → p4)) ∧ p2) ∧ p3) ∧ (p4 ∨ p4))) ∨ p1) ∨ True) ∨ (p2 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135028948726691927101256658475 : (((p5 → ((p4 → True) → ((p2 ∨ p4) ∨ (p3 ∨ (p2 → ((((p1 → True) ∨ p5) ∧ p5) → True)))))) ∧ (p1 ∧ p1)) ∨ ((p2 ∧ False) → p4)) := by
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
theorem thm_5_vars_193957894005894735826013610440 : ((p2 ∨ (p5 ∧ (((p4 ∧ (p4 ∨ p5)) ∨ p4) ∧ p4))) → ((True ∨ (((((False → (p4 → False)) ∨ p5) → False) ∨ p4) → p2)) → (p2 ∨ True))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



