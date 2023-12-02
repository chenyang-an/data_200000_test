variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149136749595921185256853993406 : (((p4 ∧ p4) ∧ ((((((True ∨ p4) ∧ p2) → p3) ∨ p1) ∨ (((True ∨ p1) ∧ p4) ∧ p1)) ∨ (p1 ∧ p5))) ∨ (p4 → ((False ∧ True) → p2))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197979188016529082977145836192 : (((p2 ∨ True) ∧ ((p2 ∨ p2) ∧ (p5 ∨ p3))) ∨ ((p4 ∨ ((True ∨ ((p5 ∨ (True ∧ (p3 ∨ (False ∧ (p2 → False))))) ∨ False)) ∨ p1)) ∨ p2)) := by
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
theorem thm_5_vars_39252631698845069882323111998 : (((False ∧ ((p5 ∧ ((True ∧ p4) ∨ (((False ∧ ((p2 ∧ p1) → p2)) → False) → p4))) → (((p2 ∨ (p3 ∧ False)) ∧ p3) → False))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49472676166681496507055176571 : (((((((p1 ∧ p5) ∨ p4) → (((p4 ∨ p1) ∨ (p4 ∧ p2)) → ((p3 ∧ p2) ∨ (True ∨ p3)))) ∨ p2) → True) → (p4 → (p2 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623044250645125968784170889501 : ((((p5 ∧ (p1 ∨ ((p2 ∨ (((p5 ∨ (p1 → True)) ∨ ((p2 ∨ p2) → p4)) ∧ (p2 ∨ ((False → False) ∧ (p2 ∨ False))))) ∧ True))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_147370339342374530059328362282 : ((((((p2 ∧ (p1 → p1)) → p4) → (p4 ∧ ((p4 ∨ p2) → p5))) ∨ (((p1 → p5) ∨ p4) ∨ True)) ∨ p5) ∨ ((p1 → p2) ∨ (False ∨ p3))) := by
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
theorem thm_5_vars_112865589655112155866126507728 : ((((p3 → (p2 ∨ p4)) ∨ (p5 ∧ (((p5 ∧ (((True → p2) → p2) → p1)) ∨ p5) ∨ (p2 → (p2 ∧ (p5 ∧ p3)))))) → p3) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190903395535869954513044733285 : (((p4 ∨ ((False → (True ∨ p1)) → True)) → (p4 ∨ p4)) ∨ (True ∧ (((False → p1) ∧ (((False → (p1 → (False ∧ p4))) → p3) ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614162177859028549141513359797 : (((((((((p5 ∨ (((p1 ∨ p1) → (p3 ∨ p3)) → True)) ∨ True) ∧ ((p5 ∧ p3) ∧ p3)) ∧ p4) ∨ p2) → (p4 ∧ (False ∧ True))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49537811878434448181679518550 : (((((p2 ∧ ((True ∨ (((p5 ∧ (p1 ∨ True)) ∨ p5) ∧ (True ∨ (True ∧ p5)))) ∧ p2)) → True) → (p2 ∨ p2)) → ((p3 → False) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52618951969573118065246547202 : (((((p4 ∧ p1) ∧ p2) ∨ (p2 → ((False ∨ ((p3 ∨ p3) ∧ p4)) ∧ p4))) ∨ ((((False ∨ (True → p4)) → (False ∨ p2)) ∧ p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114894757842708716413051893308 : (((p3 ∨ (False ∧ (((p3 ∧ ((p4 ∨ p3) ∨ (False ∨ True))) ∧ True) ∨ p5))) ∨ (False → (p2 ∨ ((p5 ∨ True) ∧ (p5 → p2))))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113274570446809288537152419443 : (((((p1 ∨ ((p3 ∧ p2) ∨ p2)) ∧ ((False ∨ (p3 → (False ∨ p3))) → p3)) ∨ ((True ∨ p3) → (True ∨ p4))) ∧ (p1 → p1)) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715242654497941196977060009390 : ((((p1 → (p5 ∧ ((p4 ∨ p3) ∧ p1))) → ((((False ∨ False) → p2) ∨ (p1 ∧ (True → (p5 ∨ p2)))) ∧ ((p1 ∨ p4) ∧ (p2 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342044213772360253711551656959 : (p2 → (((((p2 ∧ (((True ∨ p1) → p3) → p4)) ∨ (True ∨ (p2 ∧ ((p2 ∧ p4) ∨ True)))) ∨ p3) ∧ (True ∨ False)) → ((False ∧ p4) ∨ p2))) := by
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
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h22 =>
            -- False on the left can always be used.
            apply False.elim h22
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h25 =>
            -- False on the left can always be used.
            apply False.elim h25
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h28 =>
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87899004824678556077637066428 : (((True ∧ (((p3 ∨ True) ∨ p2) ∨ p4)) → ((((p4 ∨ p3) → p2) ∧ ((False ∧ p2) ∨ (p2 ∨ ((p3 → p3) ∨ p2)))) ∧ (False ∧ p5))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (((p3 ∨ True) ∨ p2) ∨ p4)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346340216609771287159563674656 : (p3 → (((p5 ∨ (p1 → (p5 → ((p1 ∨ (p5 ∨ False)) → p2)))) → ((((True ∧ (True → p5)) → (True ∨ True)) → p4) ∨ p3)) ∨ (p2 ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641510035615188214270379352237 : (((((p1 ∧ p1) → (((((p3 ∨ (p3 ∧ p3)) → ((False → p5) → p1)) → p4) ∨ p4) → ((p1 ∧ (True ∧ (False → p3))) → p5))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213653975721466472381075474311 : ((((p4 ∨ p3) ∨ False) ∨ p2) ∨ ((p3 ∨ (((((p4 → False) ∧ True) ∧ (p3 ∧ ((False ∨ p3) → p2))) → p1) → (True ∨ (p3 → True)))) ∨ p2)) := by
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
theorem thm_5_vars_312371293280541400052447600299 : (p2 ∨ (p3 → (((p5 → ((p1 ∨ ((p1 → p5) ∨ True)) → (p1 ∨ p2))) ∨ (False → p3)) ∨ ((p3 → ((p5 → (p3 → p1)) → p3)) ∧ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351411199786507606216028188809 : (p4 → ((((p2 ∨ p5) → (True ∧ p3)) → ((False ∧ (((p1 ∧ p2) → (p2 → p3)) ∧ True)) ∨ (p1 ∧ False))) ∨ (p2 → ((p2 ∧ p1) ∨ p2)))) := by
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
theorem thm_5_vars_139701652435851985495013471295 : ((((p4 → p2) ∧ (p1 → ((False → ((p2 ∧ (p2 ∧ (p1 → True))) → p3)) ∧ (p5 ∧ (p4 ∧ (False → p3)))))) → False) → (p3 → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232271225051996729696015231080 : (((p2 → p2) → p1) → ((((p2 ∨ ((p5 → p5) → p4)) → (((p4 ∧ p3) → p1) ∧ (p1 ∧ (True ∨ (False ∨ (p5 → p2)))))) ∧ p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388890769803616151964506190654 : (((((p3 ∨ ((((p5 ∧ (p3 ∧ p5)) ∧ (p2 ∨ (p4 ∧ (False ∨ False)))) ∨ True) ∧ True)) ∨ ((False ∧ True) → ((True ∧ p1) ∨ p5))) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67768830524401504900181635215 : ((p2 → (((((p5 ∧ p2) ∧ False) ∨ p1) ∨ (p2 → (p1 → (((p2 ∧ p4) ∨ p4) ∧ (p5 → (False → (p4 → (p4 ∨ p4)))))))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134104159706987526608979316169 : ((((((((((p3 ∧ (p3 ∧ False)) ∨ p5) → p2) ∧ p5) ∧ False) ∨ ((p4 ∨ p4) ∨ p2)) ∧ p2) ∧ (p2 → p3)) ∨ p2) ∨ ((p2 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111950431928427580257592565881 : ((((p4 ∧ ((p2 ∧ (p2 ∨ (p4 ∨ p4))) ∧ p2)) ∧ (p5 ∨ (((p4 → True) ∨ (False ∨ False)) ∨ (p2 → (p4 → False))))) ∨ True) ∨ (True ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150028923980133452013985336775 : ((p5 ∨ ((p1 ∨ p5) ∧ ((((p5 ∨ p3) ∨ ((p2 → p1) ∧ True)) ∧ p1) ∧ ((p5 → (False → False)) → p5)))) ∨ (p4 → (p5 → (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185340780684160765051494320557 : ((p4 ∧ (((p5 ∧ p3) → (p1 ∨ ((p5 → True) → False))) ∨ p5)) ∨ ((p3 → (p3 ∨ p2)) → (False → ((p2 ∨ ((False ∧ p4) ∨ True)) → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115322673235065722690061648261 : ((((False ∨ p2) ∧ ((p3 ∨ (p1 ∧ p5)) → (True ∧ p1))) → (p5 ∧ (((p3 ∧ False) → (True ∨ (p1 ∧ p1))) ∨ (p3 ∨ False)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224930809153158274299047244981 : ((p5 → (p5 ∨ p5)) ∧ ((((p5 ∨ p5) ∨ (((p3 → (p5 ∨ p2)) → p4) ∨ p2)) → (((p4 → p3) ∨ p4) → p3)) → ((p2 ∧ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355904518880045552084404512255 : (p5 → (((((p1 → p3) → False) → (((((p1 → (p3 ∧ True)) → p3) ∧ ((True → p4) ∧ p2)) ∨ False) ∨ False)) ∨ p2) → (p3 → (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614223225887020533532400539279 : ((((((((p4 ∧ p2) ∨ (p1 ∧ ((p3 → True) → p4))) → (p4 ∧ ((p2 ∧ p1) ∨ p2))) ∧ (p2 ∨ p4)) → (p3 ∨ (p4 → p1))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258154188523573598742644724447 : ((p4 ∨ p4) → ((p3 ∨ ((((p1 ∧ (p2 → False)) ∨ (p2 ∧ (((p1 ∧ False) ∧ p3) ∨ ((p4 ∧ True) ∧ (False ∨ p1))))) ∨ p1) ∨ p4)) ∧ True)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595421723170928652701968744220 : ((((((((((p2 ∧ p2) ∧ True) ∨ True) ∨ (p3 → False)) ∧ p3) ∨ False) ∨ (p1 ∨ (True → ((p5 ∨ (p3 ∨ True)) ∨ (p2 → p4))))) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25336268134094170323668882802 : ((((False ∧ p3) → p2) → ((((False → p2) ∧ p2) ∨ ((True ∧ (p2 ∧ p4)) → ((p3 → False) ∨ (p5 → (p4 → (p5 ∧ p4)))))) ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264299245778589984367652011770 : (True ∧ ((((p5 → (False ∧ True)) ∨ True) → False) → (((p3 ∧ True) ∨ (True ∧ (p1 → (p2 ∧ ((((False ∨ p2) ∧ p1) ∨ p5) ∧ p1))))) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    have h6 : ((p5 → (False ∧ True)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : ((p5 → (False ∧ True)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40183299241306957457975241838 : (((((((p4 ∨ p1) ∨ False) ∨ True) → ((p3 ∧ ((p3 → ((p3 → p1) ∧ False)) ∧ ((False ∧ p4) ∨ True))) ∨ (p3 ∨ False))) ∧ True) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122722206412397322505216639193 : ((((p1 ∨ p2) ∨ ((False ∧ False) → (((((p1 ∨ ((p5 ∧ True) → p3)) → (True ∨ p5)) ∧ p5) ∨ False) ∧ p2))) → (p3 ∧ False)) → (False ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ p2) ∨ ((False ∧ False) → (((((p1 ∨ ((p5 ∧ True) → p3)) → (True ∨ p5)) ∧ p5) ∨ False) ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : ((p1 ∨ p2) ∨ ((False ∧ False) → (((((p1 ∨ ((p5 ∧ True) → p3)) → (True ∨ p5)) ∧ p5) ∨ False) ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the left can always be decomposed.
    let h14 := h11.left
    let h15 := h11.right
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h10
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28500221551300635026424171505 : ((True ∧ (p5 ∨ ((p1 ∧ (((((False → p1) ∨ (p2 ∧ p1)) → (True ∧ False)) ∧ ((p5 ∨ ((p4 ∨ p2) → True)) ∧ p5)) ∧ True)) → p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : ((False → p1) ∨ (p2 ∧ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : ((False → p1) ∨ (p2 ∧ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h18 := h6 h16
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320469836767243774134159455387 : (p4 ∨ ((p1 → p1) → ((((p3 ∨ (p3 ∨ False)) → False) ∧ (True ∧ p3)) → ((((p5 ∧ True) ∧ p3) ∨ False) ∨ ((p1 ∧ (p4 → p1)) → False))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ (p3 ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62420447380122347781028860488 : ((p3 ∧ ((((p2 → p2) → p5) → (p2 ∨ p3)) → (((p1 ∧ p4) ∨ (((p2 → False) ∨ (p4 ∧ p5)) ∨ (True ∧ (p2 → p2)))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118908976418392077671568152527 : ((True → (p2 → ((p1 ∧ ((((p2 → (False → (True ∨ p3))) → True) ∧ p1) ∧ (p4 → False))) ∨ (p1 ∨ (p1 ∨ (p1 → p2)))))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230788059705133132973398617218 : (((True ∧ p4) ∨ p2) → (p2 ∨ ((((((p1 → (p2 → ((False ∧ False) ∧ (False ∨ p3)))) ∧ (p3 → p1)) → False) ∧ p5) ∧ True) ∨ (True → p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793622997319751801603630546037 : (((True → (p4 ∨ ((False → (p3 ∧ (True → (((((p2 ∨ p4) → p2) ∧ p3) ∧ p2) ∨ False)))) ∧ ((p2 ∨ (p3 ∨ (p5 ∨ p4))) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53187863621741504686415966091 : (((((True → (((p3 ∨ p2) → False) ∨ p2)) ∧ p5) ∧ (p2 → p4)) ∨ (p4 ∨ ((((True → p3) → ((False ∨ False) ∨ p3)) ∨ False) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622978577974287167687138330470 : ((((p5 ∧ (((p2 → False) → True) ∧ (((p4 ∧ (p1 ∨ (p1 ∨ False))) → (p1 → p1)) → ((False → (p3 ∧ True)) ∧ (False ∧ p4))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119379321590519419533790157860 : ((p3 → (p1 → ((True ∧ ((p4 ∧ (p3 ∧ (((p1 → ((True ∨ p3) ∧ (p3 ∨ p2))) → p2) ∨ (p2 ∨ False)))) ∨ True)) ∨ p5))) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_64500618327874602219331577788 : ((p1 ∨ (((((True ∨ (p2 ∨ p5)) ∧ ((False ∧ p3) ∧ (p4 → p1))) ∧ True) → False) ∧ (((False ∧ p3) ∨ p1) ∧ (p2 ∨ (p3 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674416729203884696699778409931 : ((((p2 ∨ (p2 → (((False ∨ ((p5 ∧ ((False → (True ∧ p1)) ∨ (p3 → p1))) → (False → p3))) → True) ∧ p5))) → (p2 ∨ (p4 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777853682052245198811174293439 : (((p1 ∨ ((False ∨ (p3 ∨ (p5 ∧ True))) ∨ ((p3 → (((p3 ∨ (((p2 ∧ (p4 → p2)) → p5) ∧ False)) ∨ (p1 ∧ p3)) → p5)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261440186453191461291055524383 : ((p5 → p2) → (((((p2 ∧ ((False ∧ (False ∧ p2)) ∧ p5)) → (True ∨ (p5 ∨ (p1 ∧ True)))) → (((p1 → p3) → p3) → p5)) ∧ p3) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 ∧ ((False ∧ (False ∧ p2)) ∧ p5)) → (True ∨ (p5 ∨ (p1 ∧ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h5
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : ((p1 → p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h14
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148607608017496882654974675211 : ((((((True → p1) → True) → ((p2 ∨ False) ∧ p3)) ∧ p4) → (False ∧ (False ∨ ((p4 → False) ∨ (p4 ∧ p3))))) ∨ (False → (p1 → (False ∧ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133850143236601762731107696338 : (((False ∧ ((((p4 → (p5 ∨ p1)) ∧ p5) ∨ (((p5 ∧ p3) → ((p2 ∧ False) → True)) → p1)) ∧ (p5 ∨ True))) ∧ p4) ∨ (False → (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255957911111923555163987825104 : ((True ∨ p2) → (True → (((p4 ∨ p4) → p2) ∨ ((p5 → ((p3 ∨ (False ∧ p5)) → p2)) ∨ (p1 → (((p2 ∨ (p5 ∧ p4)) ∨ True) ∨ False)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667930950067615530202203156244 : ((((p2 ∨ (False ∨ ((p5 ∨ (((False → (((False ∧ p1) ∨ (True ∧ False)) ∨ p3)) → False) ∧ (False → p3))) ∨ p4))) ∧ ((p3 → p5) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136671553001019161159231584457 : (((p3 ∨ (p3 ∨ True)) → ((p3 ∨ (((True ∧ (p5 → p3)) ∨ p4) ∨ (False ∨ ((p2 → (p3 ∨ True)) ∧ p3)))) → p5)) ∨ ((p1 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763002862950183457931036903923 : (((p3 ∧ ((p2 ∧ ((p5 ∧ p3) → p1)) → (((p1 ∨ ((False ∧ True) → ((((p1 → p3) → p3) → True) → (False → False)))) ∧ p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44332790329945009812486382949 : (((((((((p3 ∧ False) ∧ (p5 ∨ False)) ∨ (True ∧ False)) ∨ (p5 ∧ p2)) ∧ False) ∨ True) → ((p4 → ((p1 ∨ p3) → p3)) ∧ p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47507946440505010332889184701 : (((p2 ∨ (((p5 ∧ p3) → ((p5 ∨ p3) ∧ (((((p1 ∨ p4) ∧ (p4 ∧ p4)) ∧ False) ∨ (p2 ∨ p3)) ∧ p4))) → False)) ∨ (p3 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112105487739461992252330757672 : ((((p1 ∨ p1) → ((True ∨ ((p3 → ((p4 → True) → p3)) ∧ ((True → (p1 → (False ∨ p2))) ∨ False))) → (p2 → p3))) ∨ p5) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113198647786141475183492489476 : (((((((True → p4) ∨ p5) ∧ (False ∨ ((p4 → ((p2 ∧ p4) → ((True ∨ p1) → False))) → False))) ∧ False) ∨ p5) ∧ (p1 ∨ p1)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114990712385361803066586660224 : (((((((p2 ∧ p5) ∧ p5) → True) → (True ∨ True)) ∧ (True ∧ p2)) ∧ (((False ∧ p4) ∧ True) ∨ (((p4 ∨ p4) ∧ p2) ∨ p3))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338349963266502957249395946590 : (p1 → ((((p5 ∨ p2) ∨ p3) ∨ p5) ∨ (((p3 ∧ p3) → p1) → (p3 ∨ (((p5 ∨ (True ∨ p2)) ∨ ((p1 ∧ (p1 ∨ p5)) ∧ False)) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_113250584201471955425983902036 : ((((((True ∧ p4) → ((p4 → p5) ∨ True)) → (((p5 → p4) ∨ p3) ∨ ((p2 → True) ∨ False))) ∨ (p5 ∧ p2)) ∧ (p5 → False)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52266722113417317702520801848 : (((p5 ∨ (p5 ∨ (((p1 ∧ p3) ∧ ((p3 → (p3 ∨ False)) ∨ p2)) → (p2 ∨ p5)))) → (((((p4 ∧ p2) ∨ p3) → p1) ∧ False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321080761669118828342779441627 : (p4 ∨ (p1 ∨ (((p2 ∧ p5) ∧ p4) → (p1 ∨ (((((False ∨ (p1 ∧ (p3 ∧ (p5 ∧ (p4 ∨ p5))))) ∧ p1) ∨ (p5 → p2)) ∨ False) ∧ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341764853810147432366864734924 : (p2 → ((True → ((p5 ∨ (p4 ∨ p2)) ∧ ((p1 → (((p1 → ((p3 → False) → False)) ∨ True) ∧ p4)) ∨ ((p5 → p2) → p2)))) ∨ (p2 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148672324122680301510468388824 : (((((False ∨ (False ∧ p3)) ∧ (p5 ∧ p3)) ∨ p4) ∨ (False → (((((False ∨ p4) ∨ True) ∧ p2) ∨ p5) ∨ p1))) ∨ (((p4 → True) ∧ p5) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247732017356350634423344379909 : ((p1 ∨ False) ∨ (((((p4 ∧ (True ∧ (False ∧ ((p3 → p4) ∨ False)))) ∨ True) ∧ True) ∨ p4) ∨ ((p3 ∨ (((False ∨ p1) → p4) ∧ p4)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_44167193980044175310438938784 : (((((((p1 ∨ True) ∧ False) → p3) ∨ (True → ((True ∨ p2) ∨ ((p5 → (False ∧ (p2 ∨ True))) ∧ p3)))) → ((p1 ∧ p4) → p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653047551907736732719061532779 : ((((True → ((p1 ∨ (((p1 ∧ p5) ∧ (((p2 ∨ p5) → p3) ∨ p3)) → (p4 ∨ ((True ∧ p1) → p3)))) ∨ (p1 ∨ p5))) ∧ (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185515839131790302699546171812 : ((p3 ∨ (((p3 ∧ (((p2 ∨ p2) → p5) → p1)) ∧ False) ∧ True)) ∨ ((p5 → (p2 ∨ (p2 → p1))) → (((p3 ∧ True) ∨ p5) → (p1 ∨ True)))) := by
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
theorem thm_5_vars_156891837968955842537782843849 : (((((p4 → (p1 ∨ (p3 ∧ p2))) ∧ (False → (((p3 ∨ p1) ∧ (False → p2)) ∨ p4))) ∨ False) ∨ p5) ∨ (p4 → (((True ∧ True) ∨ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41418309815684275854756335500 : ((((p1 ∧ (((p5 ∨ p4) ∨ (p2 → (p5 ∨ ((p3 ∧ p4) ∧ False)))) → p5)) ∨ (((p4 → True) ∨ p2) → (p5 ∧ (p5 ∨ p2)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328916823067345286558617124233 : (True → ((((False ∧ (p5 ∨ p2)) ∧ True) ∨ (p1 → p3)) → (((p3 → ((True ∧ False) ∨ (p4 ∨ p4))) ∨ (((p1 → p1) ∨ p3) ∨ p3)) ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766992677010359283475290548774 : (((p4 ∧ (p1 → (((p2 ∨ ((p1 → p2) → (p1 → (p2 ∨ p2)))) → (p4 → (p5 ∨ ((False ∧ p3) → (p1 → False))))) ∧ (p4 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50770108199898005715101404386 : (((p1 ∨ (((p2 ∨ False) ∧ (((p1 ∨ (True ∨ ((p2 → (p1 ∨ p4)) ∧ True))) ∨ p4) ∧ p5)) ∨ p3)) → (p1 ∧ (p1 ∨ (p1 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197043102779624392617511244155 : ((((p1 ∨ p3) ∧ (p1 ∧ (p2 ∧ p3))) ∨ True) ∨ ((False → ((False ∧ p4) ∨ p3)) → (True ∨ (p1 ∨ (False ∧ ((p3 → (p4 → True)) → p4)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172906829991540579520354895375 : ((p2 ∧ ((p4 → (((p5 ∧ p3) ∨ (p1 ∧ False)) ∧ p1)) ∧ ((p3 → p3) ∧ False))) ∨ (p3 → (p5 ∨ (p3 ∨ ((p5 → False) ∧ (True ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111718480081947980947568021197 : ((((((p3 ∨ (False ∨ p3)) → (p4 ∧ False)) ∨ (((p1 ∧ p2) ∧ (((p5 ∧ p1) ∨ (False ∨ p5)) → p5)) ∧ p1)) → p5) ∨ True) ∨ (p4 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205642291232782591650590730665 : (((p4 ∧ p4) ∨ (p5 ∨ (p3 ∧ p4))) ∨ (((True ∨ False) ∧ (((p3 ∧ (p3 → (p2 ∨ False))) ∨ (p3 ∧ (p2 ∧ p3))) → (True ∨ p2))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37175762624491597769922290213 : (((((p5 ∨ ((p5 ∨ p4) → ((((p1 ∧ p5) → p2) ∧ False) → p4))) ∧ (p4 ∨ (True ∧ ((p2 ∧ (p1 ∧ p3)) ∨ p2)))) ∧ True) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52225071645206381384037542142 : (((True ∧ (True ∨ ((False → (((True ∨ p4) ∧ True) ∨ (p3 ∨ (p5 ∧ False)))) ∨ p4))) → (p5 → (p1 → ((p1 → (p3 → p3)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662839957284884841107450317968 : (((((True ∧ (p1 → p2)) ∧ (p3 ∧ (((p1 ∨ p3) ∨ (p4 ∧ ((p2 ∧ p1) → (True → p3)))) ∨ (p1 ∧ (p3 ∧ p5))))) → (p2 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43064064926412487148060155405 : (((((((p1 ∨ p4) ∧ p4) ∧ (((p2 → (((((p1 → p4) → p1) ∨ False) ∨ False) ∧ True)) → (p3 → p2)) ∨ p2)) → p3) ∧ True) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213103844438011371204210147038 : ((((p1 ∨ p4) ∧ p5) ∧ p5) ∨ (((True → ((p3 ∧ ((False ∧ (p2 → (p5 ∨ p3))) ∨ False)) ∧ p4)) → False) ∧ ((p3 → (p4 ∨ p3)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227613102809213737571207022361 : ((False ∧ (True ∨ p5)) ∨ ((p3 ∧ (p2 ∨ (((p5 ∨ p1) ∨ (p3 ∨ False)) ∧ (p4 → p4)))) ∨ ((p1 → ((True ∧ (p2 ∧ p2)) ∨ True)) ∨ p2))) := by
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
theorem thm_5_vars_43953895358516410122528470700 : (((((False → p1) ∨ (p3 ∨ ((p3 ∨ (p1 ∨ ((((p2 ∧ True) ∧ (p3 ∨ p1)) → False) ∨ (p4 → p3)))) ∧ p5))) ∨ (p5 ∧ p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137076435882556503519746617029 : (((p5 → p1) → (((p2 ∨ ((((True ∧ True) ∨ (p4 → p4)) ∧ p3) ∧ ((True ∨ (p2 ∧ p1)) ∨ p1))) ∨ False) ∧ p4)) ∨ (p4 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245424500029025963047211832978 : ((p2 ∧ p4) ∨ (((True → (p3 ∧ False)) ∧ ((p4 ∨ False) ∨ (p5 → ((p2 ∧ p5) ∧ True)))) ∨ (True ∨ (p5 → (p1 ∨ ((p3 ∧ p5) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136379648951894387067630346689 : ((((p3 ∨ p5) ∧ (p3 ∨ False)) ∨ ((p1 → (((p5 → p1) ∨ p5) ∨ (((p1 ∧ p5) → (p2 ∧ False)) → p1))) ∧ False)) ∨ (False → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661556330028373370749594608067 : (((((((p4 ∨ (p1 ∨ (p3 ∨ p1))) ∧ (True ∧ True)) → (((p2 ∧ (p5 ∨ p1)) ∧ p4) ∧ p3)) ∨ ((p4 ∨ p5) → p1)) → (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136586288226810238417338889533 : (((p4 ∧ (p5 ∨ True)) ∨ ((((p1 ∨ p4) ∨ ((((p1 → (True ∧ (p1 ∨ p2))) ∧ p2) ∨ p5) → p3)) ∨ False) ∨ True)) ∨ (p3 → (p3 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240433381787988483636950305228 : ((p5 ∨ True) ∧ (((p1 ∨ ((((p2 ∧ True) → (p1 ∨ ((False ∨ p3) ∨ False))) ∧ True) ∨ ((p2 ∧ True) ∧ (p1 ∧ True)))) ∨ True) ∧ (p1 → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265832617971642564186366770698 : (True ∧ (p5 ∨ ((((p3 ∨ ((True ∨ (p4 ∨ p5)) → False)) ∧ (True ∧ p2)) ∧ ((p3 → p5) ∨ (p4 ∧ (p4 → False)))) → (p5 ∨ (False → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h5.left
    let h18 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111659196151992453976066727369 : ((((p3 ∧ ((((True ∧ (p1 ∧ (True ∨ ((p4 → False) ∧ (p2 → p4))))) ∧ (p1 ∧ (p2 → p1))) ∧ p5) ∨ p3)) ∨ True) ∨ p3) ∨ (p3 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171815295815145169201183715592 : (((((p1 → (True ∨ p4)) ∧ (False ∨ True)) → (True ∧ (p2 → (p5 → False)))) → p2) ∨ (False → ((((p1 ∨ (p2 ∧ p4)) ∧ p2) ∧ p4) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804660558634328762082605091021 : (((p3 → (((p4 ∨ p1) → (p2 ∧ p3)) → (True → ((p1 ∧ p5) ∨ ((((p4 ∨ ((True ∧ (False → True)) ∨ True)) ∧ p4) → p3) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346586814311107049472400624699 : (p3 → (((p1 ∧ (((((((p2 ∨ p5) ∨ p2) ∨ False) ∨ (p1 ∨ (p1 ∨ True))) ∨ (p2 → p1)) ∧ p4) ∨ p2)) ∧ p5) ∨ ((p1 ∨ p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



