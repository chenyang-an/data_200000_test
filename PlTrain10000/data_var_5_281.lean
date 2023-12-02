variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670664587072153582820197602092 : (((((p4 ∨ p3) → (False ∧ (p3 ∨ (False → (True ∧ (p1 → ((((False ∨ p5) → (True ∨ p5)) ∧ p5) ∨ True))))))) ∨ (p1 ∧ (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158937013014866633074504112556 : ((p2 ∨ (((p4 ∨ p3) ∧ ((((p5 ∧ False) ∨ False) → (((p2 ∨ p5) ∧ True) → p3)) ∧ p4)) → p1)) ∨ ((p2 → p1) ∨ (p4 → (p2 → True)))) := by
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
theorem thm_5_vars_168582362735255655608505894828 : ((p2 ∧ (((p4 → (True → (p1 ∧ p2))) → False) → ((False → p3) ∨ ((p1 → p5) → p3)))) → ((True ∧ ((p1 ∨ p2) ∧ True)) ∨ (p4 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250991073816981750471657614547 : ((p1 → p5) ∨ ((((p3 → p2) ∨ ((True ∨ (p1 ∨ (((p3 ∧ (p4 → (False → p5))) ∨ False) ∧ p5))) ∧ True)) → ((p2 ∨ p5) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147991032465237279822860158469 : ((((False ∧ ((p5 ∨ p5) → (p3 ∨ (((True ∨ True) ∧ (True → p4)) ∧ (p5 → p5))))) ∨ False) ∨ (p4 → p5)) ∨ (True → (False → (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64128581984042074925443427130 : ((False ∨ ((((False → p4) ∨ p5) → False) ∨ ((False ∨ ((((p1 ∨ ((p4 → True) ∧ p5)) ∨ p1) ∧ (p3 ∨ p5)) ∧ (p4 ∨ p3))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44482045681491660998466832982 : ((((p2 ∨ (((((p5 ∧ p1) ∧ False) → p1) → p3) → (p2 ∨ False))) → ((False ∨ ((p2 ∧ p5) → (p5 → (False → False)))) ∨ p2)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229912536650432051626678647753 : ((p5 → (p2 → p4)) ∨ (p2 → ((p3 ∧ (((((p5 ∨ True) ∧ p5) ∨ p4) → p3) ∧ p2)) ∨ (True ∨ ((p3 ∨ (p3 ∨ (True → p5))) ∧ True))))) := by
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
theorem thm_5_vars_733843501151512520932222048164 : ((((p5 ∧ p4) ∧ (True ∧ (((p3 ∧ p2) ∧ p3) ∨ ((True → p5) → ((True → (p5 ∧ (p3 ∨ p4))) ∨ ((p5 → p4) → (p1 → p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231961356973457811310267959083 : (((p1 ∨ p3) → False) → (((((p3 → False) ∨ p5) ∧ ((True ∧ (True ∧ p2)) ∨ p3)) ∨ (p1 ∨ p4)) ∨ (p3 → (p5 ∧ (False ∨ (p3 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354583613645142083660348620863 : (p5 → ((((True → p1) ∧ ((((p1 ∧ ((p5 ∨ (p2 → p5)) → p4)) ∨ (p5 → False)) ∧ ((p2 ∧ p2) ∧ (p3 ∨ True))) ∧ p1)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809958490728772737879869839301 : (((p5 → ((((p4 ∨ ((p4 ∨ p2) ∧ (((True → p1) ∨ False) ∧ p1))) → False) ∧ ((p4 → (p3 ∨ False)) → p4)) ∨ (p5 ∧ (p2 ∨ p5)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763143770013654765288875568519 : (((p3 ∧ ((p5 → (p5 ∨ p3)) → (p2 ∨ ((p5 ∨ ((((p4 → p4) ∧ (p4 → True)) ∨ p3) ∨ ((p5 ∧ p5) ∧ (p5 → p1)))) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315024508027967073960884941807 : (p3 ∨ (((p3 → p2) → ((True ∧ p4) ∨ (True → p4))) ∨ (((((p2 → p1) ∨ True) ∨ ((p5 → False) ∧ False)) → p1) ∨ ((p2 ∨ p4) ∨ True)))) := by
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
theorem thm_5_vars_669766516860915726406008308076 : ((((((p5 → True) → ((p4 → p5) ∧ ((True ∧ ((False → p4) → p3)) → p1))) ∨ ((p4 ∧ p5) ∧ (p1 ∧ p2))) ∨ ((p4 → True) → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_613437261042819646757741641875 : (((((p1 ∨ (((False ∧ (p4 → ((p5 ∨ ((p2 ∨ True) → (p4 → True))) ∧ p2))) ∨ p3) → ((p1 → False) ∧ p3))) → (p5 ∧ p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_598675253543531682111456839172 : (((((p1 → (True ∨ p4)) → ((p2 ∧ ((p3 ∧ False) ∧ p5)) ∧ (p2 → (p4 → (((p4 ∨ (p3 ∨ False)) ∨ False) ∨ (p3 ∨ p4)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316559946172961565123126691470 : (p3 ∨ (p3 ∨ ((((True → ((p4 ∧ ((p3 ∨ ((p5 ∨ False) ∧ True)) ∧ p4)) → (p5 ∨ False))) → p5) ∨ ((p2 ∨ p1) → True)) ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39364986957476884221646693656 : (((p3 ∧ ((((p1 ∧ (True → (((p2 ∧ (p4 ∧ p3)) ∨ p1) ∨ (p4 ∨ p2)))) ∨ p5) ∨ (p2 → (True ∨ p2))) ∨ (False → True))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189821820736343017984499488359 : ((False → (((p2 ∧ (p5 ∧ p5)) ∧ True) ∧ (False → p5))) ∧ ((p1 ∨ p4) ∨ (p5 ∨ ((p4 ∨ ((p5 ∨ False) ∨ (p3 ∧ True))) ∨ (p5 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60059173570477971125267775833 : (((p2 ∨ p1) → ((p1 ∧ ((False ∧ ((p2 ∧ (p3 ∧ (False ∧ p2))) ∨ (p1 → p5))) ∧ ((((p4 ∧ True) ∨ p1) ∨ p2) → False))) ∨ True)) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322323775776703446439008744303 : (p5 ∨ (((p1 ∨ ((p1 ∧ False) ∨ ((True ∨ p4) → ((p4 → (p3 ∨ (False ∧ ((p5 ∧ p2) → p1)))) → (p3 ∧ p1))))) ∧ (p1 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137622326504317354139342134608 : ((False ∨ ((p5 → ((p2 ∨ p2) → ((p5 → p4) ∧ ((p1 ∨ ((True ∧ p4) ∧ p4)) ∨ ((p4 → p1) ∨ p3))))) ∨ p3)) ∨ ((p1 ∧ False) → p4)) := by
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
theorem thm_5_vars_115755355503197838442341619484 : (((p3 ∧ (p3 ∨ (True ∨ (p2 ∨ True)))) → (False ∨ (((((False ∨ True) → (p5 → (p1 ∨ (p2 → True)))) ∧ p3) → p2) → p2))) ∨ (p3 ∧ p2)) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((False ∨ True) → (p5 → (p1 ∨ (p2 → True)))) ∧ p3) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : (((False ∨ True) → (p5 → (p1 ∨ (p2 → True)))) ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h22 := h15 h16
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h28 : (((False ∨ True) → (p5 → (p1 ∨ (p2 → True)))) ∧ p3) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h29
          -- Implications on the right can always be decomposed.
          intro h30
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h31 =>
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h33
            -- True on the right can always be proven directly.
            apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h34 := h27 h28
        -- One of the premise coincides with the conclusion.
        exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199345307386684417268879487103 : ((((p4 ∧ ((False → False) ∧ p1)) → True) ∨ True) → ((p1 → p4) → (p5 ∨ (p2 → (True → (((p5 ∨ True) ∨ False) ∧ ((p1 ∨ p2) ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57306138638016770601827225589 : (((True ∧ (True ∧ p2)) ∨ (p1 ∨ ((((p1 ∧ (p4 ∨ p1)) → p5) ∨ (p3 ∧ (((True → p2) → (p2 → p1)) → (p3 → True)))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707745804072632065422265690708 : (((((False → p5) → ((False ∧ p1) ∧ (p2 ∧ p4))) ∨ ((True ∨ (False → ((((True ∨ p5) → p1) ∨ True) ∧ (False ∧ p4)))) ∨ (False → p2))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_55474737368260499868180808297 : (((((False ∧ True) ∧ False) ∨ (p2 ∨ p2)) → ((p5 → ((((False → ((p1 ∨ p4) → p2)) → True) ∨ (p5 ∨ (p2 → False))) ∧ False)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164815622828203009543876032893 : ((((p1 ∧ p3) ∨ (((((p3 ∧ False) ∨ (p3 ∧ p5)) ∨ False) ∧ p3) ∧ (True → True))) ∨ p5) ∨ (((False ∨ (p1 → p5)) ∧ (p1 ∧ p2)) → p1)) := by
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
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345386228279706699542117921086 : (p3 → (((p5 ∨ ((((False ∧ (p3 ∨ ((p4 → False) ∧ False))) ∨ ((((False ∨ p1) → True) → p1) ∧ p5)) → (p2 ∨ p2)) → p2)) ∨ p3) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51031941470563564521886840685 : (((p5 ∧ ((((p3 ∨ p3) ∧ p4) ∨ (False → (True ∧ p1))) ∧ (False ∨ ((p2 → True) ∧ p3)))) ∧ (p3 ∧ (p2 → ((False ∧ p2) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138841450171291267108725940614 : (((p5 ∧ ((((p5 ∨ p2) ∧ (False ∧ (p1 ∨ (False ∨ p1)))) → (p3 ∧ (p5 ∨ False))) ∨ (p4 ∧ (True ∨ True)))) ∧ p1) → ((p5 → False) → p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165080767519665323773253657836 : (((True ∨ (p4 → (p3 ∧ ((p2 → (((p3 ∨ p3) ∧ p4) ∧ (p5 ∧ p3))) ∨ p5)))) → p2) ∨ ((False ∨ (False ∧ p5)) → ((p2 ∧ p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255570593793539000970629395571 : ((p5 ∧ p3) → (((((p5 ∨ (p2 → True)) → False) ∧ p5) → p4) → ((((p5 → p4) ∨ (True → p1)) ∨ (p5 ∧ (p5 ∧ p4))) ∨ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689458893731814263938434517376 : (((((((p1 → p3) ∨ (p1 ∨ True)) → (p2 → (p3 ∧ p1))) ∨ (False ∧ (p4 → p2))) ∨ (p2 → ((p5 → p5) ∨ (p4 ∨ (p1 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313250327882594460131062988321 : (p3 ∨ (((True ∨ p4) → ((((((p1 ∨ True) ∧ (False → p3)) → p3) ∧ p5) ∧ (((p1 ∧ False) ∨ (p2 ∧ True)) → p1)) ∧ (p2 → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43996652112293459561490651962 : (((((((p3 ∧ p5) → ((False ∧ False) ∨ p4)) ∧ ((p1 ∨ p5) ∧ (False → ((p2 → p3) ∧ (p2 → True))))) → p3) → (p3 ∨ p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343162145399797077636537675840 : (p2 → ((p1 ∧ (p2 → False)) ∨ ((p3 ∨ ((p1 ∨ p1) ∨ (((((True ∧ False) ∨ p5) → False) ∨ (p4 → True)) ∨ (p2 ∨ p1)))) → (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161508594460888533632948030852 : ((p4 ∧ ((True ∧ (False ∨ (p4 ∧ False))) ∨ ((p3 → p2) → (((p1 ∧ p2) ∧ p4) ∧ (True → p4))))) → ((p1 ∧ (True ∨ p1)) → (p3 ∨ p1))) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65822851353809139193234190210 : ((p4 ∨ ((False → ((p3 → (p5 ∧ p4)) ∨ p2)) → (p5 ∧ ((p1 ∧ (p5 ∨ (((p5 → (p5 ∨ p4)) → p3) → p3))) ∨ (p1 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230389193180185741395840285805 : (((p3 ∨ p3) ∧ p3) → (((p4 ∨ False) ∨ (((p2 ∧ ((p4 ∨ p3) → ((True ∧ p1) ∧ p4))) ∧ ((p4 → True) ∨ p3)) ∨ p5)) ∨ (p3 ∨ False))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231576632132025239480382483613 : (((p5 → p4) ∨ p4) → ((((p4 ∧ p3) ∨ (p2 ∨ (p3 ∨ False))) ∧ p4) ∨ (((p3 → p5) ∧ (p1 ∧ (p3 ∨ True))) → ((p4 ∨ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199581528393962358761686385320 : ((((True → (p3 ∨ (p2 → p2))) ∨ p1) → p3) → (p4 → ((p3 ∨ ((p1 ∧ p1) ∧ p1)) ∨ (((p5 ∨ p1) ∧ (False ∨ p3)) ∧ (p5 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True → (p3 ∨ (p2 → p2))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138727722108462286274435872881 : ((((((p5 ∨ True) → p2) ∨ True) ∧ ((p1 → False) ∧ (p1 ∧ ((((p5 ∧ True) ∨ p5) → (p4 → p1)) ∧ p2)))) ∧ p4) → ((p5 ∨ True) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h15 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h16 := h9 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h7.left
      let h19 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h25 := h18 h24
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h27.left
    let h30 := h27.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
      have h38 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h34
      -- We have shown the premise of h32, we can now drive its conclusion.
      let h39 := h32 h38
      -- False on the left can always be used.
      apply False.elim h39
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h30.left
      let h42 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h42.left
      let h44 := h42.right
      -- Conjunctions on the left can always be decomposed.
      let h45 := h44.left
      let h46 := h44.right
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h47 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h48 := h41 h47
      -- False on the left can always be used.
      apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311062989193873024197684811279 : (p2 ∨ ((False ∨ p4) ∨ (((((p4 ∨ ((((False → False) ∧ (p4 ∨ p3)) ∧ p1) ∧ p4)) ∨ p5) → p5) ∧ p4) ∨ (p4 ∨ ((p4 ∧ False) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25375601514101642110437384716 : ((((p4 ∨ p1) → p1) → ((p2 ∨ p3) ∨ ((((p5 → p2) → (((((True ∧ p5) → p4) ∨ p1) → p5) ∨ p1)) → (p5 ∨ p2)) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126113461590439811581032015106 : ((True ∧ (((p3 ∧ (((p5 → p1) → ((p4 ∧ (False ∨ (False ∨ p3))) ∧ (False ∧ p5))) → True)) → p4) ∧ ((p2 ∧ p3) → p4))) → (p1 → p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165497928235727670815901850442 : (((p5 ∧ ((p3 → p4) ∨ ((p3 → (p4 ∨ False)) → False))) ∨ (((p3 ∧ p2) ∨ True) ∨ False)) ∨ ((p4 ∧ (p3 ∧ (p4 ∧ p3))) ∨ (True → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117269204949039104674452113038 : ((False ∧ (((p5 ∨ p4) → ((p3 → (((p1 ∨ p5) ∧ ((False ∨ p4) ∨ p5)) ∧ p5)) ∧ (((p2 → p5) → True) ∧ True))) ∧ True)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310314771850491679433873563542 : (p2 ∨ ((True → (p4 → (((p4 ∧ (p3 ∨ p3)) ∨ p2) ∨ p2))) ∨ ((p5 → ((p4 ∨ True) → p5)) ∧ (True ∨ (False ∧ ((False → False) ∨ p3)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66040437074630548256291427086 : ((p5 ∨ ((p2 ∨ (p3 ∨ (((p2 ∧ (p3 → p2)) ∧ p4) → ((p1 ∧ (p5 ∨ (p4 ∧ (p3 → (p5 ∨ (True ∧ p5)))))) → p3)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351828451494764812783340200645 : (p4 → ((p3 ∧ ((((False → False) ∧ (False ∨ p2)) ∧ (p3 ∧ p2)) ∨ p5)) ∨ (p4 → ((p2 ∧ False) → (p3 ∧ ((p5 → p1) ∧ (p1 ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h3.left
  let h10 := h3.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147065817701292263226851005735 : ((((p2 → (((p4 ∧ (p4 → p3)) ∧ p1) ∨ p4)) ∨ ((((p3 ∨ False) ∧ p1) ∨ (True ∨ True)) ∨ p4)) ∧ p2) ∨ ((p1 ∧ p3) → (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173126173355534738870190742901 : ((p2 ∨ (False ∧ ((p5 ∨ (p1 ∧ (False ∨ p2))) → ((p3 ∨ p4) → (p1 → p2))))) ∨ (p5 ∨ (p2 → (p5 ∨ ((p4 → False) ∨ (p2 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392925290827046860847161774318 : (((((p1 ∨ (True ∨ p3)) → (((p3 ∧ (((p3 ∧ p2) ∧ ((p1 ∧ p5) ∨ p1)) → False)) ∨ p4) ∧ ((p1 ∨ p5) → (p5 ∧ p5)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_265649356379916895741858090156 : (True ∧ (p2 ∨ ((((False → False) ∧ ((p2 ∨ (p5 ∨ p5)) ∨ (False → ((p5 → ((p2 ∨ p5) ∧ p2)) → False)))) → p4) ∨ (p5 → (p1 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135310477305391847079914989171 : (((((p5 ∧ p3) → ((True ∨ (False → (((p3 → p1) ∧ False) ∨ p1))) ∨ (p1 ∨ True))) → p5) ∧ ((p5 ∨ True) → p3)) ∨ (True ∧ (True ∧ True))) := by
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
theorem thm_5_vars_537077606290384972822803038 : (((((((p1 ∧ (p3 → p5)) → (p3 ∧ ((p3 ∧ p5) ∧ p1))) ∧ ((p5 → p2) → (p4 ∧ p1))) ∧ True) ∧ (p3 ∧ p5)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49176317273991708269746550098 : ((((False ∧ ((p1 ∨ p5) ∧ False)) ∧ (((((p2 ∧ False) ∧ (False ∨ False)) ∨ True) → ((p3 ∧ p5) ∨ p3)) ∧ p5)) ∨ (False ∧ (True ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113526451545983422175490211215 : ((((p5 ∧ (((p4 ∨ p5) ∨ p2) → (p3 ∨ False))) ∨ (p4 → ((p3 → p1) ∨ ((p4 ∧ (p4 ∨ p5)) ∧ True)))) ∨ (False ∨ p5)) ∨ (p3 ∨ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126342310976683392092326706993 : ((p1 ∧ ((p5 ∧ ((p3 ∧ (p5 ∨ ((((p1 ∧ p4) ∨ p2) ∨ p3) ∨ p3))) ∧ (((p1 → True) ∨ True) → p5))) ∧ (True → False))) → (False ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h22 := h5 h21
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h24 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h25 := h5 h24
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h28 := h5 h27
        -- False on the left can always be used.
        apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h30 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h31 := h5 h30
      -- False on the left can always be used.
      apply False.elim h31
  -- Conjunctions on the left can always be decomposed.
  let h32 := h1.left
  let h33 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h33.left
  let h35 := h33.right
  -- Conjunctions on the left can always be decomposed.
  let h36 := h34.left
  let h37 := h34.right
  -- Conjunctions on the left can always be decomposed.
  let h38 := h37.left
  let h39 := h37.right
  -- Conjunctions on the left can always be decomposed.
  let h40 := h38.left
  let h41 := h38.right
  -- Disjunctions on the left can always be decomposed.
  cases h41
  case inl h42 =>
    -- One of the premise coincides with the conclusion.
    exact h42
  case inr h43 =>
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h44
      case inl h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h46 =>
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- One of the premise coincides with the conclusion.
          exact h36
        case inr h49 =>
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h50 =>
        -- One of the premise coincides with the conclusion.
        exact h36
    case inr h51 =>
      -- One of the premise coincides with the conclusion.
      exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112825849151859706953381326896 : ((((((True ∨ False) ∧ False) → p5) ∨ ((p4 ∧ ((p3 → p2) ∨ p1)) → (p1 ∨ (p5 ∨ ((p1 ∨ (True ∨ p3)) ∧ True))))) → p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307426883843215273260959961160 : (p1 ∨ (p5 ∨ ((p4 ∨ ((p2 ∨ p3) ∧ ((p1 ∨ p3) → ((p2 → ((((p2 ∧ (p3 ∧ p4)) → (p3 ∧ p2)) ∧ p2) ∧ p2)) → p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168397903485179454158740467266 : (((p4 → p4) ∨ (p3 → ((((False → True) ∧ True) ∧ (True ∨ (p4 ∨ (True ∧ p2)))) → p4))) → ((((True ∧ True) → p4) ∧ p1) → (p1 ∧ p4))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h13 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h14 := h7 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325823328787385111438842075733 : (p5 ∨ (p3 ∨ ((p2 ∨ ((p1 → p4) ∧ p5)) → (p4 ∨ (((p4 ∧ (p2 → (p5 ∨ False))) → (True → p4)) ∨ ((p5 → p5) ∧ (p5 → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199459987863922104599372467331 : (((p5 ∧ (p5 ∨ ((p5 ∨ True) → p5))) ∨ p2) → (p1 ∨ (p2 → ((((((False → False) → p4) ∨ p3) ∧ (p2 ∨ p3)) ∨ (p5 → True)) ∨ p4)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116861656184532878704689509672 : (((p1 → p2) ∨ ((((p2 → p3) ∨ ((p5 ∨ ((((p1 → p2) → p1) → True) ∨ True)) → ((False → p1) → False))) ∨ True) ∨ True)) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342821678334431923775520208413 : (p2 → ((((p1 ∧ True) ∨ p4) ∨ (True ∨ p2)) ∧ (p5 → (p2 → (p3 ∨ (True ∧ ((((False → (False → p2)) → p3) ∨ p5) ∨ (False ∨ p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61263690771629959942298922540 : ((False ∧ (p1 ∨ ((False ∨ (p1 ∨ (p3 → ((((p4 ∨ ((False ∨ p4) ∧ True)) ∧ p2) ∧ (((p4 → p1) → p1) → p3)) → False)))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148322781766518367423964590419 : (((p3 → ((p4 ∧ (p4 ∧ p3)) ∨ ((((p5 ∧ p3) ∨ False) ∨ (p4 → p5)) → p4))) → ((p3 ∧ p5) ∨ p1)) ∨ (p2 → (False ∨ (True → True)))) := by
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
theorem thm_5_vars_148169902947440316069947300894 : (((((True → ((p1 ∧ p1) ∨ (p5 ∨ (p5 ∨ False)))) ∨ (p2 → (True ∧ False))) ∨ True) ∧ (True ∧ (p2 ∧ p5))) ∨ ((False → (p4 ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134509046696841335402015412938 : (((((p1 → p2) ∨ (((p3 ∨ p4) ∨ ((False ∨ ((p1 ∨ (p2 ∨ p4)) ∧ (p1 → p1))) → p5)) → p2)) ∨ p5) → p5) ∨ ((False ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767338476771221697201185288263 : (((p5 ∧ (((p3 ∨ ((p1 ∧ p1) ∧ p1)) ∨ (False ∨ ((p4 ∨ ((p5 ∨ (p2 ∨ (p3 → False))) → True)) ∨ (p3 ∨ (False ∨ p4))))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_976938915366809185991241864655 : (((True ∧ (((p2 ∨ p3) ∧ (((p5 ∨ (False → p3)) ∨ (True ∧ p4)) → (((p4 ∨ p5) ∨ (True ∨ p5)) ∧ p1))) ∧ (False → (p4 ∧ p1)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : ((p5 ∨ (False → p3)) ∨ (True ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h14 : ((p5 ∨ (False → p3)) ∨ (True ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h16 := h7 h14
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638272487135166518764354929543 : ((((((((False ∨ p5) ∧ p5) ∨ False) ∧ True) ∧ ((p2 → (True ∨ p4)) ∧ ((p5 ∨ p5) ∧ ((p5 ∧ (p4 ∨ False)) ∧ (True ∧ p1))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642570720654329663938007969976 : ((((p1 ∧ (((p4 ∧ (p5 ∨ ((((p3 → p5) → (p2 ∨ p4)) ∧ (p3 → (((p3 ∧ p4) → p4) ∧ False))) → p5))) ∨ p1) ∨ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50412608667639045573781118569 : (((p1 ∧ ((p1 ∨ ((p3 ∨ p3) ∧ ((False ∧ p2) ∨ (False → ((False → p2) ∨ p1))))) ∧ (p5 ∧ p5))) ∨ (True ∨ (p4 ∧ (p3 → p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677788022397741540107079918325 : (((((p2 → (((((False ∨ p3) → p3) ∧ True) ∨ p2) ∨ (p2 ∨ (((p1 → False) ∧ p3) ∧ p1)))) → p3) ∨ (True ∨ (p2 ∧ (p2 ∧ p4)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_299366569813867599294713773962 : (False ∨ (((True ∧ p5) ∨ ((((True ∨ (((p4 → False) ∧ (p1 → ((True ∨ p3) → p4))) → p2)) → p1) ∨ (p4 ∧ p2)) → (False ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319647536337847038236384235992 : (p4 ∨ (((p3 → False) → (((p4 → True) ∨ p1) → p5)) ∨ (((p5 ∨ (False ∨ p1)) ∧ p1) → ((((True → (p1 ∧ p2)) ∧ False) → p5) ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169132724338544203741534784376 : ((p5 → (((((False → (True → False)) ∧ p1) ∨ p3) ∨ p5) → (p4 ∨ (p2 ∧ (False → True))))) → (True ∧ (((p5 ∨ p2) ∧ (p4 → p3)) ∨ True))) := by
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
theorem thm_5_vars_181815767927369327742838191079 : (((((p3 ∨ (p4 ∨ p4)) ∨ True) ∨ (False ∧ (p1 → p4))) ∧ True) ∧ (((p5 ∨ (False ∨ (((p4 ∨ p3) ∧ p2) ∧ p4))) ∨ (False → p4)) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81788551357516902754602306565 : ((((((False ∧ (((((p2 ∧ p1) ∨ ((True ∧ p1) → p1)) ∧ p4) → (p5 ∧ True)) → p5)) ∨ False) ∨ False) ∨ True) → ((True → p4) ∧ True)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∧ (((((p2 ∧ p1) ∨ ((True ∧ p1) → p1)) ∧ p4) → (p5 ∧ True)) → p5)) ∨ False) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616147272142985839714068096948 : (((((((True → p1) → (((p3 → p5) ∨ p3) ∧ False)) → (p4 → p3)) ∧ ((p1 ∨ ((True → False) ∧ ((p5 ∨ p4) ∨ p3))) ∧ p3)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137313965832349854057776901397 : ((p2 ∧ ((False ∨ (p3 ∧ ((p1 → (p1 → False)) → p2))) → (False ∧ ((p5 → p1) ∧ ((p3 ∧ (p4 → p3)) ∧ p3))))) ∨ ((p2 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50408357850854866460528508837 : (((False ∧ (((p4 → (False ∧ ((p3 ∨ (False ∧ False)) → True))) ∧ (p5 ∧ (p3 ∨ p3))) → (p3 → p2))) ∨ ((p5 → False) → (False ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78236043428606715017343423130 : (((p3 → ((((False ∧ p2) → ((False ∧ (p3 ∧ p5)) → p1)) → p2) ∨ (p5 → (p1 ∨ ((p3 ∨ p1) ∧ ((p5 ∧ p2) → p2)))))) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → ((((False ∧ p2) → ((False ∧ (p3 ∧ p5)) → p1)) → p2) ∨ (p5 → (p1 ∨ ((p3 ∨ p1) ∧ ((p5 ∧ p2) → p2)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172070882176268911232558527120 : (((((p2 → (p4 → p5)) ∨ (p4 ∨ (p1 ∨ p4))) ∨ (p3 ∨ p5)) → (p2 ∨ True)) ∨ ((((((False ∨ p2) → True) → False) ∨ p2) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342182934062445891994347131197 : (p2 → ((p3 → ((((p4 → p2) → ((p5 ∨ (p3 → p4)) ∨ (((p2 → False) ∧ p4) → p3))) ∧ p5) ∧ p5)) ∨ ((False ∧ (p1 ∨ p3)) → p1))) := by
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
theorem thm_5_vars_694468645751453797670676137971 : (((((p3 ∨ p5) → ((False ∨ ((p2 ∨ p5) ∧ p1)) ∧ (p3 ∨ (False → p5)))) ∨ (((True ∨ True) → ((p3 ∨ True) ∨ (p1 → p3))) ∨ False)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638431834573759428562830330525 : (((((p1 → ((p5 ∧ (p3 ∧ p1)) ∨ p3)) ∧ ((p3 ∨ ((p4 → p2) → False)) → ((p1 ∧ False) ∧ (p2 ∨ (p3 ∨ (p4 → p1)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755612734070676945460573201738 : (((p1 ∧ ((((((p3 ∨ (p4 ∧ (p4 ∨ (p2 ∧ p3)))) → (False ∧ (True ∧ p2))) ∧ False) ∨ (((p5 ∧ p3) → p3) ∨ p5)) → p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260771606776461264319198743103 : ((p3 → p5) → ((p1 → ((p1 ∧ True) → ((((p2 → False) → ((p2 ∧ p1) → p1)) → (p3 ∧ ((p1 → (True → False)) → p3))) ∨ p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113347566882171976686202634313 : (((False ∧ (p4 ∨ (p5 ∨ (p1 ∨ (p2 ∨ ((False ∨ True) ∨ (((p4 ∧ p2) ∨ p4) ∧ ((p2 ∨ p5) ∨ p1)))))))) ∧ (p5 ∨ p2)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185014797736151244166274993344 : (((p1 ∨ p1) ∧ ((p3 ∨ ((p1 → True) → False)) ∨ (True → p2))) ∨ ((p3 → p3) ∧ (((False → ((p3 ∧ p5) → p4)) ∧ True) ∨ (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167519787157167417948421755265 : ((((p1 ∧ True) ∨ (((p4 ∧ (p3 → (True → p5))) ∨ True) ∧ (False → p5))) ∧ (p4 ∨ p5)) → ((p1 → p3) ∨ (((p2 ∨ p2) ∨ True) ∨ p4))) := by
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
    cases h3
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637634546095036370655167221220 : (((((p3 ∨ (p3 → (True ∧ ((p2 → p5) → (p2 → p3))))) ∨ (((((p1 ∧ p4) ∨ True) ∧ (True → p2)) ∧ (p4 → False)) → p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640202484285976163721688931685 : ((((((False → True) → p2) → ((p2 ∧ p1) → (p5 ∨ ((p5 ∧ ((((p2 ∧ p4) ∧ False) ∨ ((True ∨ False) ∧ p3)) → p2)) ∧ p1)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226071592609684395796656601307 : (((p5 ∧ p5) ∨ p4) ∨ ((((((False → p2) ∧ p2) ∨ True) ∨ False) ∨ p5) ∧ (((p4 → (p3 ∧ (True ∨ (True ∧ p2)))) → False) ∨ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656685933106532189640156384497 : ((((((p5 ∧ (p2 → False)) ∨ (p2 → p1)) ∧ (p5 ∧ (p3 ∨ ((True ∧ ((p5 ∨ p4) ∨ p4)) ∨ (True ∨ (p4 → p2)))))) ∨ (True ∨ True)) ∨ p5) ∧ True) := by
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



