variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151209863805142737443157941460 : (((((p4 → (False ∨ p5)) ∧ p2) ∨ (((p5 ∨ ((p2 → (True ∨ True)) ∨ (p1 ∨ True))) ∨ False) ∧ True)) → p2) → (((p3 → p2) ∧ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → (False ∨ p5)) ∧ p2) ∨ (((p5 ∨ ((p2 → (True ∨ True)) ∨ (p1 ∨ True))) ∨ False) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247832678046066492828107896478 : ((p1 ∨ p2) ∨ ((((p1 ∧ ((p3 ∨ ((p3 ∧ False) ∨ False)) ∨ (p5 ∨ p5))) → (False ∨ (((p2 ∧ p4) → p5) ∧ True))) ∨ (p5 ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_617991857445798614684283141449 : ((((((p3 ∨ (p2 ∨ p3)) ∧ p1) ∧ (((True ∨ p4) ∧ (p4 → ((p3 → False) ∧ True))) ∨ (True ∧ (p2 ∧ (p3 ∨ (p2 ∨ p3)))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302908789223679496765891171610 : (False ∨ (True → (p5 ∨ ((p2 ∧ p4) ∨ (p5 → (p4 ∨ ((p1 ∨ (((((p5 → p2) ∨ False) ∧ (p5 ∧ p4)) ∧ p4) ∨ p5)) ∨ (p3 ∨ p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635475613412286021436024140443 : (((((p2 → ((p4 ∧ p2) → (((False ∨ p5) ∨ (True ∧ ((p4 → (p4 → p4)) ∨ p2))) ∨ p5))) ∧ ((p3 ∧ p2) ∨ (True ∧ p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721118134419102327632915531943 : (((((p5 ∨ True) ∨ (p3 ∨ p4)) → (p5 → (((True → (p1 → p4)) ∨ p3) ∧ (False ∨ (p3 → ((p3 ∧ (p4 ∨ True)) → (p3 → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351207884527670520651339512582 : (p4 → (((((p5 → p3) → (False ∧ (False ∧ (p2 → (p3 ∧ (True ∧ p4)))))) ∧ ((True ∧ True) ∧ (p3 ∨ True))) ∧ False) ∨ ((p5 → p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114767521615309297686517829099 : (((p3 → ((p4 ∨ p1) → ((p1 → False) ∧ ((((True → p3) ∧ False) ∧ False) → p2)))) → (p4 ∨ (p2 ∨ ((p1 → p2) → p4)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16580564733094971513783555299 : (((((True → (p5 ∨ p3)) ∧ ((p1 → ((True → False) ∨ (((p2 → p2) ∧ p3) ∧ False))) ∨ (p2 → p3))) ∧ True) ∨ ((p2 ∨ p2) → p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137885645302506858141221905683 : ((p4 ∨ ((p5 ∧ ((p1 → (p3 → p1)) → (p3 ∧ (((p1 ∨ False) → p2) ∨ (((p2 ∧ True) ∧ p1) ∨ p3))))) ∨ False)) ∨ ((p5 → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181229184051105084248349764181 : ((p3 ∧ (((((((True ∨ True) → p2) → False) ∧ p2) → False) ∨ p2) → p2)) → ((((True ∧ (p4 ∧ p4)) ∧ p1) ∧ False) ∨ (p2 ∨ (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52811316862874874426052219751 : (((((p3 ∨ ((p2 → True) → p1)) ∧ p5) → ((p3 → (True ∧ p3)) ∨ p1)) → (((p3 → p5) → p1) → ((p1 → p3) ∧ (True → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740469146918488575389627631211 : ((((p1 ∨ p5) ∨ (((p4 ∧ ((False ∨ True) → p5)) → (False ∧ ((((False ∧ (p4 ∧ ((False ∨ p1) → p1))) ∧ p5) → p5) ∧ p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314552079751736506168212422606 : (p3 ∨ (((p2 → ((p1 ∨ p2) ∧ p5)) → (((p2 ∨ p2) ∨ p1) ∧ ((p4 ∧ (p1 ∨ p3)) ∨ p4))) ∨ (((p3 → (True ∨ p2)) ∨ p3) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343573021262648983803681244306 : (p2 → ((True → False) → (((((p4 ∨ (p5 ∨ True)) ∨ p2) ∨ p3) ∧ p2) → ((p5 ∨ (False ∨ ((True ∨ p4) ∨ (p3 → (False ∨ p2))))) ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h10 := h2 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h15 := h2 h14
          -- False on the left can always be used.
          apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778797796323684556027559349434 : (((p1 ∨ (p5 ∨ (p5 ∧ (((p3 ∧ True) → ((True ∧ (p3 ∧ p1)) → (p4 → p1))) ∧ ((p1 ∨ p3) ∨ ((p5 → p4) ∧ (p4 → p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232827424052278563570602731471 : ((p2 ∧ (p3 ∨ False)) → ((False ∨ ((False → p1) ∧ p5)) ∨ (((p5 ∧ (p1 ∧ p2)) ∧ ((p3 ∧ p5) ∨ p4)) ∨ (p3 → ((p2 ∧ True) ∨ True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37571422636998966707388398722 : ((((True → (((p1 ∧ (False ∧ ((p1 ∨ p2) ∨ (p4 ∨ ((p5 ∧ False) ∧ p1))))) ∨ (p2 ∧ ((p2 ∨ p4) ∧ True))) ∧ False)) ∨ True) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351551103681017885486307639116 : (p4 → ((p3 → (((True ∨ p5) ∧ (p5 → (p5 → (p1 → True)))) → (p2 ∨ ((p2 ∧ p3) → p5)))) ∨ ((p4 ∨ True) ∨ ((p5 ∨ p2) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3269620894563711808832668922 : ((p2 → False) ∨ (((p3 ∨ p3) → (((p4 ∨ (p5 → (((p4 ∨ p1) ∨ True) ∧ (p2 ∨ p2)))) ∧ (True ∧ True)) ∧ (False → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214839117262000925665931593951 : (((p5 ∨ p4) ∨ (p1 ∧ p3)) ∨ (((p4 ∧ p4) ∨ (False ∨ (((((p1 ∨ False) ∨ (p4 → p2)) ∨ p5) ∨ p3) ∨ True))) ∨ (p2 → (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_264309477569197900539615585972 : (True ∧ (((p4 → True) ∧ ((True → p4) → False)) → ((((p5 → (False ∧ (p1 → True))) ∧ True) ∨ ((True ∧ (p4 ∧ p5)) ∨ (p1 → True))) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322339573943691947378812530580 : (p5 ∨ ((((p4 → ((p4 ∧ (p5 → p5)) → (((False → p3) → p2) ∧ (p4 ∨ ((p4 → (True ∨ p3)) → p4))))) → False) → (p3 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315509513225448043601044683906 : (p3 ∨ ((False → (p3 ∧ p3)) → ((((p5 ∨ False) ∨ p3) ∨ (p4 → (p2 ∨ (p1 → ((False → p3) ∧ (p5 ∧ (p4 → (True ∨ False)))))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261488266549608337144264678424 : ((p5 → p2) → (p4 → ((((p4 ∧ False) ∧ p1) ∨ (p2 → p4)) ∧ ((p3 ∧ (((False ∧ p5) ∧ p3) ∨ p2)) ∨ ((p5 ∨ (p5 ∨ p2)) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226001214284348221734446954773 : (((p4 ∧ False) ∨ False) ∨ (p5 ∨ ((p3 ∧ (p2 → p1)) ∨ ((p3 ∨ ((p5 → p2) ∧ p1)) ∨ (False ∨ (True ∨ (((p3 → p2) → p3) → p4))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42585194354066250721759158521 : (((p2 ∨ ((True → (((p4 → (p3 → False)) ∧ False) ∧ p2)) ∨ ((p1 ∨ p5) → (p1 ∧ (((p3 ∨ True) ∨ (p3 → p4)) ∧ False))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200933800991506463334352433936 : ((p1 ∨ (p5 ∧ (((p1 ∧ p5) ∨ False) ∨ p3))) → (((((p2 ∨ (p2 ∧ False)) ∨ (((p5 ∧ p2) ∨ p3) ∨ p1)) ∨ True) ∨ p2) ∨ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304071929340446753339078824298 : (p1 ∨ ((p2 ∨ (p5 ∧ (((((False ∨ ((p2 ∨ ((p2 ∧ (True ∧ p4)) ∧ (p1 ∧ p5))) → p3)) → p2) → (p1 → p5)) → p1) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192206942283876014331906208968 : (((((p4 ∨ ((True → True) → p2)) → p1) → False) ∧ p1) → (p2 → (p4 → ((((p3 ∨ False) ∨ (p5 ∨ p5)) ∨ ((p2 ∨ True) ∧ False)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h1.left
        let h9 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h1.left
        let h17 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344417028234476012363554085216 : (p2 → (p5 ∨ ((True → ((True ∧ (True ∨ (p2 ∨ p2))) ∧ ((((True ∨ (True → p1)) ∧ (True ∨ False)) → ((p3 → p2) → p3)) ∧ p4))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((True ∨ (True → p1)) ∧ (True ∨ False)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (p3 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h9
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300401026473924952726155251911 : (False ∨ ((p1 ∧ (((p3 → (p3 → (((((p3 → p4) → (p2 → p3)) ∧ p1) ∧ p2) ∧ (p5 ∧ p2)))) ∧ False) ∨ p3)) ∨ (p5 → (p3 → True)))) := by
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
theorem thm_5_vars_149462490308620129088522339090 : ((False ∧ (((p1 ∧ p1) ∨ ((p5 ∨ False) ∧ p5)) ∧ ((p3 → ((p4 → p1) ∧ ((True ∨ True) ∧ False))) → p5))) ∨ (p1 ∨ (p1 → (p2 ∨ True)))) := by
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
theorem thm_5_vars_90649622831644928699849616395 : (((True ∨ p1) ∧ ((((True → False) → (p1 ∧ (p2 ∧ (p3 ∨ p2)))) ∨ ((p4 ∨ False) ∨ ((p2 ∧ p5) ∧ (p5 ∧ (p4 ∧ True))))) → False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((True → False) → (p1 ∧ (p2 ∧ (p3 ∨ p2)))) ∨ ((p4 ∨ False) ∨ ((p2 ∧ p5) ∧ (p5 ∧ (p4 ∧ True))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- False on the left can always be used.
      apply False.elim h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- False on the left can always be used.
      apply False.elim h10
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h5
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h15 : (((True → False) → (p1 ∧ (p2 ∧ (p3 ∨ p2)))) ∨ ((p4 ∨ False) ∨ ((p2 ∧ p5) ∧ (p5 ∧ (p4 ∧ True))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- False on the left can always be used.
      apply False.elim h18
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h20 := h16 h19
      -- False on the left can always be used.
      apply False.elim h20
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h21 := h3 h15
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136752044664158354115022385040 : (((p2 ∨ False) ∧ ((((False → p1) ∨ p4) ∧ (p1 ∨ (p3 ∧ p4))) ∨ (((True → p3) → (p4 → p4)) ∧ (True → p5)))) ∨ ((p4 ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111261878984579679901433017317 : ((((p5 ∨ p5) ∨ ((p5 ∨ p2) ∨ ((True → (False ∧ p4)) ∧ ((p4 ∧ ((False ∧ ((p2 ∨ True) ∧ True)) ∧ False)) ∧ p2)))) ∧ False) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121786205613112926492368375064 : (((((p1 ∨ p1) → False) ∨ (((p4 ∨ p1) → (p3 ∨ False)) ∧ (False ∨ (((p5 ∧ p3) → ((False ∨ p5) → p2)) ∨ True)))) → True) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115744997003596090885942962828 : ((((p2 → p4) ∨ (p4 → (False → p4))) → (p5 ∨ (True ∧ ((p4 ∧ p5) → ((p3 → p5) ∧ ((False ∧ (True ∧ False)) ∨ False)))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317622394664343635160837512270 : (p4 ∨ (((((p1 ∨ True) ∧ (p4 → ((p4 ∨ (p3 ∧ (p5 ∧ (((((p4 → p1) ∨ p4) ∨ p2) ∧ p1) ∧ p5)))) ∧ False))) → p2) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319169337149463268413965143503 : (p4 ∨ ((((p5 → (p4 → False)) ∨ (p3 ∨ ((p3 ∧ (p2 ∧ True)) → p3))) → ((p3 → p4) ∨ True)) ∨ ((False ∨ (False ∧ (True → p1))) ∨ False))) := by
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
theorem thm_5_vars_939593176888068641486399109832 : ((((p4 ∧ ((p1 ∨ p5) → (p2 ∧ p3))) ∨ (((p2 → True) → (p2 ∧ p4)) ∧ (((p2 ∧ p5) → ((p3 ∨ False) → (p4 ∧ p1))) ∨ True))) → p4) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h9
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h14
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113885232463685268493562367550 : ((((((p4 ∨ (((((True → True) → p5) ∧ True) → (p1 ∨ False)) ∨ p2)) ∧ (False → False)) → p1) ∨ p2) ∧ ((p4 → p3) ∨ True)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126605957227718078388885691463 : ((p3 ∧ ((p3 ∧ (((p2 ∧ p2) → (p5 → p5)) ∨ p5)) → (p3 → (p3 → ((False ∨ (p1 → p4)) ∧ ((False ∧ p4) ∨ False)))))) → (p2 ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∧ (((p2 ∧ p2) → (p5 → p5)) ∨ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
  have h21 : (p3 ∧ (((p2 ∧ p2) → (p5 → p5)) ∨ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h19
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h23
  -- We have shown the premise of h20, we can now drive its conclusion.
  let h26 := h20 h21
  -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
  have h27 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h26, we can now drive its conclusion.
  let h28 := h26 h27
  -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
  have h29 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h28, we can now drive its conclusion.
  let h30 := h28 h29
  -- We need to get the right conjuct of h30 based on <expert-advice>.
  let h31 := h30.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- False on the left can always be used.
    apply False.elim h33
  case inr h35 =>
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800065238605991777862392409180 : (((p2 → ((((p2 ∧ p4) ∨ ((True ∧ p4) ∨ False)) → ((((p1 → True) ∧ (p3 ∨ True)) ∨ p5) → (True ∧ ((p3 ∨ p1) ∧ p5)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46993756587230005360996906543 : ((((((p1 ∨ True) ∨ (p2 ∨ (True ∨ (p3 → p1)))) ∨ ((True → False) → ((p4 ∧ p5) ∨ (p5 → (p2 → True))))) → p2) ∨ (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650476085357661488039682959125 : (((((((p2 → p1) → ((p2 ∨ (True → p5)) ∨ p2)) ∧ (p1 ∨ True)) ∧ (p1 ∧ ((p5 ∧ p4) ∨ ((False → p3) ∨ True)))) ∧ (p4 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177653647809876759218767877297 : (((((p4 ∨ ((True → (True ∧ False)) ∨ p1)) ∨ (p2 ∨ p2)) ∨ p4) ∧ p1) ∨ ((((False ∨ False) → ((p5 ∨ (p4 ∧ p5)) → p3)) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259481427644268501695951438249 : ((False → p4) → (p1 → ((((((((p2 ∧ p1) → (True ∧ p2)) ∧ (p4 ∨ p5)) → ((p5 ∧ p1) ∨ p3)) ∨ p3) ∧ (False → p3)) ∨ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767604347203088629420785341820 : (((p5 ∧ (((((True ∧ p1) ∨ (p3 → p1)) → p1) ∨ ((p4 ∨ (False → p5)) ∧ ((p4 → p1) → (p2 ∨ ((p4 ∧ p3) ∨ True))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301967709930506606326749585388 : (False ∨ ((True → p3) → (((p5 ∨ p4) → ((p4 → ((p2 → ((p1 ∧ p2) → True)) → p2)) ∨ ((p1 ∧ ((p4 → p3) → p1)) ∨ True))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301962870258405509159506667174 : (False ∨ ((p5 ∨ p4) → (((p5 ∨ (p4 ∨ (p3 → (p1 → (((False ∧ p5) ∧ p2) ∧ (p1 ∨ p2)))))) → ((False ∧ (p1 ∨ p2)) ∨ False)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808457607675903466016267756098 : (((p4 → (p3 ∨ (((p3 ∨ False) ∧ (((True → ((p3 → (p4 ∧ (p5 → (False → False)))) → (p1 ∨ p3))) → p2) → p1)) ∨ (p3 ∨ p4)))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113431584221700818132702284900 : ((((((((((p1 ∧ p4) ∧ p3) ∨ (p4 ∧ (p1 ∧ p4))) ∨ (p3 → p5)) → p4) ∧ (p4 ∨ True)) ∨ False) ∨ p3) ∨ (True → True)) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193457234809743427883442239244 : (((True ∧ True) ∨ (((False ∨ (p1 ∨ p3)) → p1) → p5)) → (p3 ∨ ((p5 ∨ ((p5 ∨ True) ∧ p5)) ∨ (True → (p2 → ((True → p5) → p2)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178644814604931259685129574132 : (((True → ((p4 ∨ True) → (True → p1))) → ((p5 ∨ (p3 ∧ p5)) → p4)) ∨ (((p4 → (False ∨ False)) ∨ ((p3 ∨ True) ∨ (p1 → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260541823936876684152140555413 : ((p3 → p1) → ((p3 ∧ ((((p2 → (p3 ∧ p2)) → ((((p2 → p5) ∨ (False → p2)) ∧ p2) → p2)) ∨ p5) → p1)) → (p5 → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178430127497738575851115971861 : (((((p5 ∨ (p2 ∧ True)) → (p2 → p1)) ∧ p4) ∧ (p2 ∨ (p1 → p3))) ∨ ((p3 → ((p5 → p4) ∨ True)) ∨ ((p3 → (p3 ∨ p3)) ∧ p4))) := by
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
theorem thm_5_vars_260933555134194668922715578916 : ((p4 → False) → (p1 ∨ ((p4 ∧ (True ∧ ((p4 ∨ ((p2 ∧ p3) → True)) ∨ ((p4 ∧ p3) → ((p3 → p1) ∧ p2))))) → ((p1 ∧ p3) ∨ p2)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77477570146317863112282669433 : ((((p4 ∨ p4) → ((p3 ∨ ((p5 ∨ ((p1 ∧ (((p5 ∨ p1) ∨ (p2 ∧ p2)) ∨ (p2 ∧ p1))) ∧ p5)) → (p1 ∧ p1))) ∨ True)) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ p4) → ((p3 ∨ ((p5 ∨ ((p1 ∧ (((p5 ∨ p1) ∨ (p2 ∧ p2)) ∨ (p2 ∧ p1))) ∧ p5)) → (p1 ∧ p1))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111285071930613065517499398589 : ((((False → p1) → (((((p1 → (p3 ∨ p1)) → p5) → p5) ∧ (((p2 ∨ p4) ∨ p4) ∨ (p5 ∨ (True ∨ False)))) ∧ p2)) ∧ False) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672368392647882777390186087459 : (((((((((False ∧ p3) → p5) → False) ∧ (p2 ∨ (False → False))) ∨ (((True ∧ p3) ∨ (False ∧ False)) → p2)) → p3) → (False ∨ (p4 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40773734804368481705191578918 : ((((True ∧ ((False → p1) → (p4 ∨ ((p1 → p4) ∧ ((True ∧ ((p5 → p2) ∨ (p5 → p5))) ∨ ((False ∨ True) ∨ True)))))) → p2) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54909454284443927425452492003 : ((((((p1 ∨ p2) → p2) ∧ p4) → p4) ∧ (False ∨ (((p3 → p3) → ((p3 ∧ p2) ∨ ((p5 → False) ∧ p4))) ∨ ((p4 ∧ p3) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136429996260880934354821616392 : ((((p3 ∨ (False ∧ p5)) → p5) → (p2 ∧ (((p1 ∧ (False ∧ (p2 → (False ∧ (p5 → (True ∨ p2)))))) ∨ p5) ∧ True))) ∨ ((p5 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137410955101594490584593670689 : ((p3 ∧ (p5 → (((p1 → ((False ∨ False) ∧ p4)) ∧ (((False ∨ p3) ∧ True) ∨ (p4 ∧ True))) ∧ (p1 ∧ (False ∨ p5))))) ∨ (False ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694212950297549328435966024723 : (((((p1 ∨ (p3 ∧ (p2 ∨ p3))) ∧ ((p2 → False) ∨ (True ∧ (p3 ∧ p3)))) ∨ (False → (p4 → ((p2 → ((False ∧ p5) ∨ p1)) → True)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55336910676603400199337515423 : (((p5 ∨ (p5 ∨ ((False ∧ p1) ∧ True))) ∨ (p2 → ((p5 → (True ∧ (p5 → (((p4 ∨ ((p5 ∧ p4) ∨ p5)) → p4) ∨ True)))) ∨ p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159206166319463700748982060583 : ((p2 → (((((p4 ∨ p1) ∧ True) → (False → (p5 ∨ p3))) → p1) → ((p3 ∧ p4) ∧ (p5 ∧ False)))) ∨ ((((p5 ∧ p3) ∨ False) ∧ p4) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168088377718508983752579545794 : ((((p2 ∧ (p5 → p4)) ∧ p3) ∨ ((p3 ∧ ((p1 ∧ p5) ∨ ((p3 ∨ p4) ∧ p2))) ∧ p2)) → (False ∨ (p2 ∧ ((p4 ∨ (p2 ∧ True)) ∨ True)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313933805611265662040371815807 : (p3 ∨ (((((((p5 ∨ (p1 ∨ (False ∨ (p3 ∧ p4)))) ∨ (p3 → False)) ∧ p5) ∧ (p5 ∨ False)) ∨ (p2 → (p3 ∨ p4))) ∨ True) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211418762518474871747469020078 : (((p3 → p1) ∨ (False → p3)) ∧ ((p5 ∧ ((p1 ∨ p1) ∨ ((p4 ∧ (p2 ∨ p3)) ∨ p4))) ∨ (False → (p1 → (((p2 ∨ p2) ∧ True) → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307313629481457395609813617690 : (p1 ∨ (p3 ∨ ((((((p3 ∨ p5) → p3) ∧ False) → ((p5 ∧ ((p1 ∧ (False → (True → (p3 → p4)))) ∧ p2)) ∨ p3)) → p5) ∨ (False → p2)))) := by
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
theorem thm_5_vars_53465621518016495604493500614 : ((((p3 ∧ p5) → (((p3 ∨ (True ∧ p4)) ∨ p2) ∧ (p2 ∨ p1))) → (((p2 ∧ (True ∨ (True → p4))) ∨ (p2 → (p4 ∧ False))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243010829421760506707713706141 : ((p4 → True) ∧ (True ∧ ((((p2 ∧ ((p5 ∧ p2) → (False ∨ (p3 ∧ ((False ∨ (True ∨ ((p2 → p4) ∨ p1))) ∨ p3))))) ∨ True) ∨ False) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261083272106537451512942978011 : ((p4 → p3) → (((((((((p5 ∧ False) ∨ (p2 ∧ p3)) ∨ ((True → p5) → p4)) ∨ p3) → False) → True) → False) ∨ (p4 → p1)) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135607041130093482273829187412 : ((((p4 ∨ p5) → (p1 ∨ ((p1 ∧ p4) ∧ ((((True ∧ p2) → p4) ∧ p2) → p5)))) ∨ (p3 → (p3 ∨ (p4 → True)))) ∨ ((p4 ∨ True) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149709103977356757364960841632 : ((p5 ∧ (p5 ∧ ((((p3 ∨ p2) ∧ (p2 ∨ p5)) ∨ (True ∨ ((p1 ∧ (p2 ∨ p2)) → (p3 ∧ p4)))) → p3))) ∨ (True → (False → (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190179784844595382200783753073 : (((p5 ∧ (((p4 ∨ (p3 ∧ True)) → p5) → p2)) ∧ True) ∨ (((p4 → p4) → ((p2 → (((p3 ∧ (p5 ∨ p3)) ∧ p4) → p4)) ∧ False)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187194090514542664006016694882 : (((False ∨ p3) → (p3 ∧ (p3 ∨ (((True ∨ True) ∨ p2) ∧ p4)))) → ((((p2 ∨ p2) ∨ (p4 ∨ p2)) ∨ (p5 → p3)) → ((True → False) → p1))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h8 := h3 h7
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h11 := h3 h10
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h18 := h3 h17
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h21 := h3 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769455008894481503441366839005 : (((p5 ∧ (p2 ∧ (((p2 ∨ p3) ∨ ((False ∨ ((p1 → True) ∧ False)) ∨ ((p2 ∨ (p1 ∨ (((False ∧ True) ∨ p3) → True))) → p1))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66531057872544749536979776185 : ((True → (((((p4 ∨ False) → ((True → False) ∨ False)) ∨ p2) → (True ∧ ((p4 → (p5 ∧ p2)) ∧ (((p3 → p2) → p4) ∨ p1)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113443081200205426182032144380 : (((((True → p3) ∧ ((((p4 → p5) ∨ (p4 ∧ p2)) ∨ ((True ∨ p1) → (False ∧ (p4 ∧ True)))) → p2)) ∨ p1) ∨ (p5 → False)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345458506517340447293289131254 : (p3 → ((((True ∨ (p5 → True)) ∨ ((p3 ∨ (p4 ∨ True)) ∧ ((p4 → False) ∨ (((p3 ∨ p1) → (p4 ∨ False)) ∨ p2)))) → (p3 → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612775411629851585380959586557 : ((((((p5 ∨ (p1 → p5)) ∨ ((p3 ∧ p3) → (p1 ∨ (((p3 → False) ∨ p4) ∧ ((True ∨ (p3 ∨ p3)) → p2))))) ∨ (True ∧ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_111866493526250087043077518187 : (((((True → ((((p4 ∨ (p5 ∨ p2)) → p1) ∨ ((False → p4) ∧ p4)) → p3)) ∧ p4) ∨ ((p3 ∧ False) ∨ (p1 ∨ True))) ∨ p3) ∨ (p4 → p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2814652655222295647187419080 : (((p2 ∨ (p5 → p5)) ∧ p3) → (((p3 → ((p1 ∧ p3) → p1)) → ((((p1 ∨ p4) ∧ p2) ∨ p2) ∨ p3)) ∨ ((p3 ∨ p1) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731041487892084962111025564351 : ((((p1 ∨ (True ∧ p3)) → ((p4 ∨ p1) ∧ (False ∧ ((p2 ∨ ((p4 ∨ ((p2 → p4) ∧ p3)) ∧ p4)) → ((False → (p3 → False)) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127511914187005424140572917220 : ((p4 ∨ ((((False → (p1 ∧ ((p4 ∨ (((((p1 ∨ (True → p1)) ∨ False) ∨ p5) → p4) ∧ p4)) → True))) ∨ False) → p3) → p2)) → (p3 ∨ True)) := by
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
theorem thm_5_vars_358672048088271718499552987873 : (p5 → (p4 → ((p2 ∧ (p5 → p5)) ∨ (True ∧ ((True ∧ ((((p1 ∨ (p4 ∨ p1)) ∧ (p5 → False)) ∨ (p5 ∧ p2)) ∨ p3)) ∨ (p4 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94635229349642796912009749608 : ((p3 ∧ (((((p1 → ((False ∨ ((p3 → p3) → p4)) ∨ p1)) ∧ (((p1 ∨ p4) ∨ p2) ∧ p5)) ∧ True) ∨ (p4 → (p4 ∨ p2))) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p1 → ((False ∨ ((p3 → p3) → p4)) ∨ p1)) ∧ (((p1 ∨ p4) ∨ p2) ∧ p5)) ∧ True) ∨ (p4 → (p4 ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636038479945427382302035474022 : ((((((p2 ∨ True) ∨ ((((p3 ∨ p4) ∧ p2) ∧ p5) ∨ ((False → True) ∨ (False → p4)))) ∧ ((p2 ∧ (p1 ∨ (p2 ∧ p3))) ∨ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923508656993670045562974693319 : (((((p3 → (p5 → (((p3 → True) → False) ∨ False))) → (True → p5)) ∧ (((p3 ∧ True) → (False → True)) → (((True ∨ p4) ∧ False) ∧ False))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ True) → (False → True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608336623105876550381287536969 : ((((((((p2 → p3) ∨ p3) → (((p2 ∨ (False ∨ (False ∧ p1))) → p4) ∧ (((p5 → p5) → (p1 ∧ p2)) ∨ True))) ∨ True) ∨ True) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204402125318242168645483151773 : (((p1 → (p2 ∨ (p1 ∨ p4))) ∧ p2) ∨ ((((((p5 → ((p4 → True) → p5)) ∨ ((p4 ∨ True) → p5)) ∧ p3) → p4) ∨ False) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218673870203217727569452352858 : ((True ∧ (p3 ∨ (True → p4))) → ((p4 ∨ ((((p5 → (p2 ∨ p1)) → (((p5 ∨ p5) ∨ p3) ∨ p4)) → p3) → p1)) ∨ (True ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_114287557603398749780321694047 : ((((p4 ∧ (True ∧ (p1 ∧ (((p3 ∧ p3) → p4) ∨ ((p3 ∧ p4) ∨ (False → p2)))))) → p3) ∧ ((p3 → (p5 → p3)) → p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347284209383396626011151953934 : (p3 → ((((p1 ∨ p2) → (p3 ∧ (p3 ∧ p4))) → (p4 ∨ p2)) ∨ (False ∨ ((((p4 ∨ (p5 ∨ p2)) ∧ (True ∧ p1)) ∨ True) ∧ (p4 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22159839586487344561955080813 : ((((p5 ∨ p1) ∧ (((False ∧ p2) ∧ p3) ∧ p2)) ∨ (((p2 → p2) ∨ p5) → ((False → (False ∧ (p3 ∨ (p1 → (True → p1))))) ∨ p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356659909384109488554334569081 : (p5 → ((((p2 ∨ p3) ∨ False) → (p3 → (p5 ∧ p4))) → ((p1 → ((p2 → ((True ∧ p3) ∨ p5)) ∧ p5)) → (p1 → ((p1 → p4) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116788424347285040296805374042 : (((p1 ∨ p4) ∨ (((p2 → p4) → p3) ∧ (((p2 ∨ p4) ∧ p3) → ((p3 ∧ p4) ∨ (((p4 ∧ (p3 → p3)) ∧ p3) ∧ p3))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



