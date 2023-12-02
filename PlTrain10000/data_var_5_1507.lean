variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65356377099447123067183646570 : ((p3 ∨ ((p2 → ((p4 → (False → (((p5 → p4) ∧ (p5 ∨ p5)) ∧ p2))) → p3)) ∨ (p1 ∨ ((((p3 ∨ p5) → p3) ∨ p1) → True)))) ∨ p1) := by
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
theorem thm_5_vars_114650214395226848935097272023 : ((((((p3 ∨ ((False ∧ True) → (False ∨ False))) ∧ p5) ∧ True) → (p2 ∧ (p4 ∨ p5))) ∨ ((False ∧ (p2 ∧ (p5 → False))) ∧ p1)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_524958060411535465877275965103 : (((True ∧ (True ∧ (((((p1 ∨ (True ∧ p3)) → (True → p5)) ∧ ((p3 ∧ p4) ∨ ((True ∧ p4) ∨ p4))) ∨ p1) ∨ (p1 → (p4 ∨ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66842166988338113911886783865 : ((True → (p3 → (((True ∨ ((True ∧ p1) ∧ True)) → (p3 → ((p1 ∨ (p2 ∧ (False ∨ p4))) ∧ False))) → ((p5 ∨ p5) ∨ (p2 → False))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ ((True ∧ p1) ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121475562659904661185454385451 : ((((((p4 ∨ (p2 → p5)) → True) → (((p5 ∨ (p1 ∧ (False ∧ (p4 ∨ ((p1 ∧ p3) ∨ p5))))) ∨ p5) ∧ False)) → p1) → False) → (False ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ (p2 → p5)) → True) → (((p5 ∨ (p1 ∧ (False ∧ (p4 ∨ ((p1 ∧ p3) ∨ p5))))) ∨ p5) ∧ False)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∨ (p2 → p5)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((((p4 ∨ (p2 → p5)) → True) → (((p5 ∨ (p1 ∧ (False ∧ (p4 ∨ ((p1 ∧ p3) ∨ p5))))) ∨ p5) ∧ False)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : ((p4 ∨ (p2 → p5)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h9
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137995548426490216324226846901 : ((p5 ∨ (False ∨ ((p1 ∨ (p1 → ((False → p2) ∨ (p3 ∨ p5)))) → ((True → p2) ∧ (p1 ∧ (True → (p5 ∨ p1))))))) ∨ ((False ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60445192022160538528092309145 : (((p5 → True) → (p5 ∧ (p4 ∨ ((True → p3) ∨ (((p1 → False) ∨ p4) ∨ ((((p2 ∨ p2) ∨ False) ∨ p5) ∨ ((p2 ∧ p5) ∧ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731014897447327076730468479682 : ((((False ∨ (True → p1)) → (p5 → (((p1 ∧ ((((p2 → p1) ∧ p3) ∧ (p1 ∧ p4)) ∧ p4)) ∨ ((False → (p4 ∧ True)) → p2)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68872701306057249605665698450 : ((p4 → (False ∧ (((p5 ∨ (p1 ∨ (p4 → False))) ∧ p4) ∧ (p2 ∨ (p5 ∨ ((((p2 → ((False ∨ False) ∨ True)) ∧ p2) → p2) ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9644550009673278244138727854 : ((((p3 → True) ∧ ((False ∨ p1) → (True ∧ ((True ∧ (False ∧ (p2 ∧ (p2 → (p5 ∨ True))))) ∨ (((False ∧ False) ∨ p2) ∨ p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354573514995144082082240843284 : (p5 → ((((p2 ∨ (p2 → (True ∨ (p1 ∧ ((False ∧ (True → (p4 ∨ True))) → ((p4 ∨ p4) ∨ p3)))))) → (p1 ∨ (False ∧ p4))) ∧ p5) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178559562794543801737471160185 : ((((p5 ∨ ((p5 ∨ p1) ∧ p5)) → False) ∧ (((p1 → p5) ∧ p5) ∧ p2)) ∨ ((p5 ∧ (False ∧ (((True → (p3 ∨ True)) → False) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196779101890622574612950983597 : ((((p4 ∧ p3) ∧ (p5 ∧ (p1 ∨ p1))) ∧ True) ∨ ((((False ∨ True) ∨ ((p5 ∨ True) → (((False ∨ False) ∨ p3) → (True ∨ p4)))) ∨ False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183810453845407632055828870153 : ((((False → ((p4 → (p4 ∨ p5)) ∨ (p1 → p5))) ∨ p4) ∧ False) ∨ (((((p4 → (False ∧ p3)) → (p3 → False)) ∧ p2) ∨ p5) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58585039411362917495842421699 : (((True → p5) ∧ (((p1 ∨ ((((False ∧ p4) ∨ (p2 ∧ p4)) ∨ p5) ∨ ((((p4 → True) ∧ p1) → (p5 → p3)) → p4))) ∧ p2) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667735122025268743787787132974 : ((((p5 ∧ ((p4 ∧ ((((p5 ∧ p4) → ((p1 ∨ False) ∨ p1)) → (p1 ∨ (p2 ∧ True))) → p2)) ∨ (p4 ∨ p2))) ∧ (p4 ∨ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608773484364373318019111748512 : (((((((p4 ∧ ((((False → (((False ∨ False) ∧ p5) → p4)) ∨ p5) → p5) → (True → p5))) → False) ∨ ((p2 ∨ p5) → p1)) ∨ p5) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_199488393631798703948191108348 : (((p5 ∨ ((p4 ∨ (p3 ∨ p3)) ∨ False)) ∨ False) → ((p4 → p5) → ((((True ∨ False) ∨ False) ∨ p5) → ((p1 → False) ∨ (p5 → (False → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h9
            -- Implications on the right can always be decomposed.
            intro h10
            -- False on the left can always be used.
            apply False.elim h10
          case inr h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Disjunctions on the left can always be decomposed.
              cases h12
              case inl h13 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h14
                -- Implications on the right can always be decomposed.
                intro h15
                -- False on the left can always be used.
                apply False.elim h15
              case inr h16 =>
                -- Disjunctions on the left can always be decomposed.
                cases h16
                case inl h17 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- Implications on the right can always be decomposed.
                  intro h18
                  -- Implications on the right can always be decomposed.
                  intro h19
                  -- False on the left can always be used.
                  apply False.elim h19
                case inr h20 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- Implications on the right can always be decomposed.
                  intro h21
                  -- Implications on the right can always be decomposed.
                  intro h22
                  -- False on the left can always be used.
                  apply False.elim h22
            case inr h23 =>
              -- False on the left can always be used.
              apply False.elim h23
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- Implications on the right can always be decomposed.
        intro h31
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h35
            -- Implications on the right can always be decomposed.
            intro h36
            -- False on the left can always be used.
            apply False.elim h36
          case inr h37 =>
            -- Disjunctions on the left can always be decomposed.
            cases h37
            case inl h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h39
              -- Implications on the right can always be decomposed.
              intro h40
              -- False on the left can always be used.
              apply False.elim h40
            case inr h41 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h42
              -- Implications on the right can always be decomposed.
              intro h43
              -- False on the left can always be used.
              apply False.elim h43
        case inr h44 =>
          -- False on the left can always be used.
          apply False.elim h44
    case inr h45 =>
      -- False on the left can always be used.
      apply False.elim h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46842703832162171894653156874 : ((((((True ∧ (p5 → True)) ∧ p3) ∧ (((p5 ∧ ((((p5 → p2) ∨ p5) ∨ (p1 ∨ p4)) ∨ p4)) ∧ p2) → False)) ∧ p1) ∨ (p1 → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47392546693189683137401319425 : ((((p3 → p3) → (p5 ∨ ((p1 ∨ (p1 ∧ True)) ∧ (((p3 → p5) → (p2 ∨ ((p1 → True) ∨ p3))) → (p1 ∧ p5))))) ∨ (p4 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345620723428635769257834014981 : (p3 → ((True ∧ (((((True ∨ (p1 → ((p5 ∧ p3) ∨ p3))) ∧ ((p5 ∨ p1) ∨ (p1 ∨ p4))) → p1) ∨ p4) ∨ (p1 ∨ (True ∨ True)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654202315019296082953346071310 : ((((((p3 → (True → (((p5 → True) → ((False → p4) ∨ (p2 ∨ (p5 ∧ p4)))) → ((p1 ∨ p5) ∧ p5)))) ∨ p4) ∨ True) ∨ (p5 → True)) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159504241578468506699220056410 : ((((p4 ∧ p2) ∧ (False → (((((p2 ∨ True) ∧ p2) ∨ p3) ∨ ((True ∧ p1) ∨ True)) → p5))) ∧ p4) → ((p1 ∧ p2) ∨ ((True → p3) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46290497492744167578373500931 : (((((p4 ∨ False) ∧ (((((p3 → p5) ∧ True) → (p1 → ((False ∨ p1) → p2))) ∧ p1) → False)) ∨ ((p1 ∨ p5) ∨ False)) ∧ (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803237466029826297260724573353 : (((p3 → (((True → ((p2 ∧ p2) ∧ (((True ∧ p2) ∨ (False → p2)) ∨ (((p4 ∧ False) ∨ p2) ∨ ((False ∨ True) ∨ True))))) → p4) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14844076205990561125240907220 : (((((p2 → (((False ∨ p4) → p2) ∨ (p4 → p5))) → p4) ∧ (((p5 ∧ p1) ∧ (p2 ∨ (False → (p2 → False)))) ∨ p3)) ∨ (True ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51519658239899356618631217446 : ((((True ∨ False) ∨ ((((True ∧ p2) ∨ p4) → (False ∨ ((False ∧ p1) → (True → p4)))) ∨ p5)) → (p2 ∧ (((p3 → False) ∨ p3) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166786449550437747742232108347 : ((p5 → (False ∧ (((p1 ∧ p4) → True) ∧ ((((p2 ∨ p3) → p3) → p2) ∧ (p1 → True))))) ∨ ((False → p4) ∨ (p1 ∧ ((p4 ∨ p4) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114042096888302142117636617782 : (((((p4 ∨ ((p1 ∧ ((p4 ∧ p3) ∨ True)) ∨ (p4 ∨ ((p2 → False) ∨ p5)))) ∧ False) ∨ (True ∧ True)) ∨ (p4 ∨ (False → p3))) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798855406590552524387642760740 : (((p1 → ((True ∧ p3) ∧ (((((True ∨ p3) ∨ ((p4 → p3) ∨ True)) ∨ (True ∨ p3)) ∧ (((False ∨ p3) ∧ (p1 → p1)) ∨ p5)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695467613688753855910522840068 : ((((((((False → (True ∧ p5)) ∨ p3) → (True ∨ False)) ∨ p4) → (p1 ∨ p3)) → ((True ∨ (True ∨ (p5 ∧ (p3 → p1)))) ∧ (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728068704405265815921845532702 : ((((p4 ∨ (p2 ∨ p2)) ∨ ((((p1 ∨ ((p5 ∨ p5) ∨ True)) → ((((p3 → (True ∨ p1)) ∨ p2) ∧ p1) → p5)) ∨ p5) ∨ (p5 → p5))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731901093083729163746040502571 : ((((p5 → (p2 ∧ p3)) → ((p5 ∧ (((p3 ∧ p5) → p1) ∨ p4)) ∨ (p4 → (((p5 ∧ False) → (p2 ∨ (p5 ∨ p4))) ∨ (p1 ∨ p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166037805810748825274450409752 : (((p3 → False) ∨ ((((p4 ∨ p1) ∧ (p5 ∨ p1)) ∧ (((p1 ∨ False) ∨ True) → p1)) ∨ p3)) ∨ (p2 → ((p4 → ((False ∨ p4) ∨ p2)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47492649270433526148915626946 : (((False ∨ (p3 ∨ ((((p3 ∧ ((p3 ∧ p5) → (True ∧ p4))) ∨ (p3 ∧ (p3 ∨ p2))) → ((p5 → p3) ∧ p5)) ∧ True))) ∨ (False ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308737997630272097470798680325 : (p2 ∨ ((p3 → ((p1 ∨ ((p2 ∧ (p4 ∨ (((p3 ∨ p4) ∧ p3) → p1))) ∧ (p2 ∨ False))) ∨ ((p4 ∨ (p3 → True)) → (p3 → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248726825331203072140373225806 : ((p3 ∨ p2) ∨ (p1 ∨ (((p1 ∨ (p2 ∨ p5)) ∨ ((True ∨ ((p2 ∨ ((True → p1) ∨ (p4 → p1))) ∧ (True ∧ p2))) ∧ p5)) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_340721292679165056746948730807 : (p2 → (((False ∨ ((p2 ∨ ((False ∨ (p4 ∧ (((p4 → p1) ∨ False) → (p4 ∨ p1)))) ∧ (p4 ∨ p2))) → ((p1 ∨ True) ∧ p1))) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66502036998169564628065710180 : ((True → ((p4 ∧ (((p5 ∧ True) → (((p3 → p4) ∧ True) → (p4 ∨ (p4 ∧ (False → (p5 → p5)))))) → ((p3 ∨ p2) ∧ p4))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193409138888935690026878185296 : (((True ∨ p3) ∧ (p1 → (False → ((p2 ∨ p3) ∨ p2)))) → ((p2 ∨ False) → ((p3 ∧ (p2 → p1)) → ((((p4 → False) ∨ p5) → p4) ∨ p3)))) := by
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
  cases h2
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336197320441890858791171670740 : (p1 → ((((((p1 ∧ p2) → False) → ((p5 → (p1 → (p5 → (p5 ∨ (p5 ∨ p5))))) ∧ (p5 ∧ (p4 ∨ p5)))) → p5) ∨ (True → True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64986022159465170601224443255 : ((p2 ∨ ((p2 → ((False → p1) ∨ False)) → (p1 → (((p5 ∨ p2) ∨ ((True ∨ p4) → ((p4 → True) ∧ p3))) ∨ ((p4 → True) ∨ p5))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135745439651209257860824664469 : ((((((p1 ∧ p3) → True) → p3) ∨ (((p5 ∧ False) ∨ p5) ∧ (p4 ∧ p4))) ∨ ((p1 ∨ ((p1 ∧ False) ∧ p3)) ∧ p1)) ∨ (p1 → (p3 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165245323109319859900608130850 : (((p1 ∨ (p4 → (((True → False) ∨ (p3 ∧ p4)) ∧ ((p5 ∧ p1) ∧ p1)))) ∨ (p2 → p1)) ∨ (((p5 ∨ p1) ∨ True) ∨ ((p2 ∨ p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615720111571172645239670675375 : ((((((p1 → p4) ∧ ((p5 ∧ True) ∨ (p3 ∧ ((p5 ∧ (p3 ∧ False)) ∧ p1)))) ∧ ((False → ((p2 ∧ True) ∧ p4)) ∨ (p4 ∧ False))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_204973680228105066948251056209 : (((p2 ∧ ((p5 → p5) → p4)) → p5) ∨ (((((False → p4) ∨ (True ∧ (p3 → True))) ∧ p2) ∨ p2) → ((False ∨ p1) ∨ (p2 → (p3 ∨ True))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231498047353218821671157231259 : (((p3 → p4) ∨ p4) → ((p5 → p3) ∨ ((p3 ∧ p4) → (((False ∧ (p4 → (p1 → (p3 ∨ True)))) ∨ (True → True)) ∨ (p3 ∨ (p3 ∧ p3)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138239032588218989980921385699 : ((p2 → (((p5 ∨ p3) ∧ (p2 ∧ ((p3 ∧ p5) ∨ False))) ∨ (True ∨ (True → (p5 → (True ∧ ((p5 ∨ False) ∨ p5))))))) ∨ (p3 ∨ (p1 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725704474103940468907134951992 : (((((False ∨ p2) ∧ p5) ∨ (((((p1 → False) ∧ p5) → (True ∧ p2)) → False) ∨ (True → (((False ∨ (p1 → (False ∧ p3))) ∨ False) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73877432007105169940643425119 : (((((p2 → (((p5 ∧ p5) → (True → True)) ∨ p3)) → False) ∧ ((((True → p1) → p5) ∧ (p2 ∧ (p1 → p5))) → (True ∨ True))) ∨ False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → (((p5 ∧ p5) → (True → True)) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h5
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206499636057919950340805986982 : ((p5 ∨ ((p4 → False) ∨ (p2 → p4))) ∨ ((p5 → ((((False ∧ p1) ∨ (True ∨ p2)) ∧ p4) ∨ (p2 → ((False ∧ p4) → p3)))) ∨ (p3 ∧ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747321957099174470224266371477 : ((((p5 ∨ p4) → (((p1 → (False ∧ p3)) → ((p5 → (((False ∧ ((p4 → p5) → p1)) → p2) ∨ (p3 ∧ True))) → (p3 → p4))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2368162188452820081759376009 : (((p4 ∧ ((p3 → p5) ∧ ((p5 → p5) ∧ p1))) ∧ (True ∧ False)) ∨ (((((True ∨ p4) → p4) ∨ p1) ∨ p5) → ((p2 ∧ p5) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_113080316123940310704526376563 : (((p4 ∨ (((p4 ∧ (((False ∧ True) ∨ p3) → p4)) → ((p1 ∧ (p1 ∧ p5)) → (p1 → (p1 → p2)))) → (p5 → p3))) → False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205294793850392135995698349255 : (((p4 ∧ (False ∧ p5)) ∨ (p5 → p4)) ∨ (p2 → ((p5 ∨ (((p5 → ((p1 → ((p5 ∨ False) → p3)) → (False ∧ p4))) ∧ p4) → p4)) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67326145786860203374695838203 : ((p1 → (((((False ∨ (((True ∨ ((False ∧ p5) ∨ p3)) ∧ p3) ∨ (p4 → (p4 ∧ False)))) ∧ p4) ∨ ((True ∧ p2) → p3)) ∨ False) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37805729915961953047839779763 : ((((p1 ∧ (True ∨ (((False → p4) ∧ p5) ∨ (p1 → (p3 → ((p1 → (p4 ∧ (p5 ∨ p5))) ∧ ((p2 ∧ p5) → p4))))))) → p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351052591483467744217325261557 : (p4 → (((p2 ∨ (p1 → ((((True ∧ ((p3 → False) ∨ (p3 → (p2 → p5)))) → (p3 ∨ (p3 → p2))) ∨ p2) ∨ p4))) → p3) → (p3 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ (p1 → ((((True ∧ ((p3 → False) ∨ (p3 → (p2 → p5)))) → (p3 ∨ (p3 → p2))) ∨ p2) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191808303930476146576850198376 : ((p2 ∨ ((p5 ∧ (False → True)) → (False ∧ (p2 ∨ p1)))) ∨ ((p3 → p4) ∨ ((p3 → p5) ∨ ((False ∨ True) ∧ ((False ∧ False) → (p1 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46297403249490857199534275981 : (((((((((p4 ∧ (((p2 ∧ p4) ∨ p4) → True)) → p3) ∧ False) ∨ (False ∧ False)) ∧ p4) → p2) → (p5 ∧ (p1 ∨ p3))) ∧ (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54856446612825777308589882906 : (((((p5 ∧ (False ∧ p4)) → p5) ∧ p2) ∧ ((p3 ∧ (p4 ∧ (p3 → (False → ((p5 ∧ True) → ((p2 → p5) ∨ p3)))))) ∨ (p3 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609099981808194922998248501219 : ((((((((p5 → (p4 ∨ p5)) → p5) → False) ∨ ((((p3 ∨ (p1 ∧ p4)) ∧ p3) ∧ p5) → ((False → (True → True)) → p1))) ∨ p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66757146804909706653272884175 : ((True → (p2 ∧ ((((((((False ∧ (p5 ∧ p5)) ∨ True) → True) ∨ p1) → p4) ∨ (p2 ∨ ((p2 ∧ p4) ∧ True))) → p1) ∨ (p4 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350175998773637962299884904659 : (p4 → (((p3 ∨ (p2 → ((p5 → False) ∧ p1))) → (((p1 → (False → (p1 → p2))) → p2) ∨ ((False ∧ p4) → ((p4 → p2) ∨ p2)))) ∨ p5)) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56272352745332552970892103640 : (((p4 → ((True ∨ True) ∧ p2)) ∨ (((((p2 ∨ (p5 ∨ ((p2 ∧ p1) → p5))) ∨ (True ∧ True)) → (p5 → p3)) ∨ (p4 ∨ p5)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116506648294587884235958595093 : (((p4 ∧ False) ∧ ((False ∨ (p2 ∨ p5)) → (p1 → (p2 ∧ (p4 ∧ (False ∧ (((p4 ∨ ((False ∧ p1) → p4)) ∧ p4) ∧ p5))))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104502149318280011184947350118 : (((((((p5 ∨ (p3 ∧ p2)) ∨ (p4 ∨ ((((p3 ∧ p4) → p1) ∧ (p1 ∨ p4)) → True))) → p3) ∧ False) ∨ p4) ∨ (p5 ∨ True)) ∧ (True ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714560225939530396940464461091 : (((((p2 ∧ True) ∨ ((True ∧ p1) → False)) → (p2 ∧ ((((((p4 ∧ (p4 → True)) ∧ (False ∧ p5)) ∨ p5) ∨ p1) → (p4 ∨ p2)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254383691599168992304940413296 : ((p2 ∧ p4) → (p5 → (((p1 → False) → ((p2 ∨ p5) ∨ (True ∨ p3))) → ((((False ∨ p3) ∧ (True ∨ p1)) → p1) ∨ (p4 ∧ (p5 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624110103590610653958537431192 : ((((p2 ∨ ((p4 ∨ p2) → (p4 → (((False → (p3 ∨ p3)) ∨ p1) → ((p3 ∨ (True ∨ (((p4 → p5) ∧ p5) ∧ p4))) ∨ True))))) ∨ p2) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232806140871438929646542893625 : ((p2 ∧ (True ∨ p2)) → ((p1 → ((p2 ∧ (((True ∧ (p2 ∧ ((p5 ∨ p5) → (p2 ∧ False)))) → False) → (p1 ∧ False))) ∨ (True → p1))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166866607117540394047862926709 : (((((False ∨ True) → ((p2 ∨ (((True ∧ p2) → p1) ∨ p4)) ∧ False)) ∧ (p1 ∨ False)) ∧ p1) → ((p5 → ((False ∨ p1) ∧ (p5 ∨ p4))) → p3)) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803804643356137185704632947039 : (((p3 → (((True → ((p2 ∨ p4) ∨ (((p2 ∨ p1) ∧ ((p1 ∧ p1) ∧ False)) ∨ (((p5 ∨ p4) ∨ p2) ∧ p4)))) ∨ True) ∨ (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646477331068288173344978199399 : ((((p1 → (((p4 → (False ∨ (((p3 → ((p4 ∨ p3) → p2)) ∧ ((p5 → False) ∧ (True ∧ p2))) ∨ p1))) → p5) ∧ (False → True))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44891966420712922502047163471 : (((((p2 → True) → p1) → (((False → ((p5 ∨ p4) → ((p4 ∧ p2) ∨ True))) ∨ (((p5 ∨ p5) → (False ∨ p4)) ∨ p5)) ∧ p3)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118625022178063535525452772675 : ((p4 ∨ (((True ∧ ((p1 → p1) ∨ p3)) → p4) ∨ (p4 → ((False ∨ ((p1 → (p1 → True)) ∨ p5)) ∨ (False ∨ (p5 ∧ p3)))))) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679695965791366646511977555786 : ((((((((((p5 → p4) ∧ ((True → (p3 ∧ p5)) → (p2 ∧ p2))) ∧ False) ∧ p5) ∨ False) → False) ∨ False) → (p4 ∧ ((p5 ∨ p2) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157331354846137364684602994484 : (((False ∨ ((p1 ∧ ((p1 ∨ p2) ∨ (False → p3))) → ((p1 ∧ (p1 ∨ (p3 ∨ p1))) ∨ False))) → p2) ∨ (((p4 ∧ (True ∧ True)) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198679412865899003649565618257 : ((p4 ∨ ((p2 ∧ (p2 ∧ False)) ∨ (p4 ∧ False))) ∨ (((True ∧ ((((False ∨ (p5 → p5)) → (p5 ∨ p3)) ∨ True) ∨ (p3 ∨ p4))) ∧ False) → p5)) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714687820919026100536616565493 : (((((p4 ∨ p4) → ((False ∨ p4) → p2)) → ((p1 ∨ ((p5 ∧ (p3 ∨ (p5 ∨ (p2 → (p1 → p5))))) ∧ ((p2 ∧ True) ∧ p4))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318891624050598315794515214659 : (p4 ∨ ((True ∧ (((p4 → (p3 ∨ (False ∨ ((p2 ∨ (False ∨ (p4 → (True ∨ p3)))) ∧ True)))) ∧ True) ∨ (p4 → p4))) ∨ ((p4 → False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116662716375588679656111106215 : (((p4 → p1) ∧ (p1 ∧ (p3 ∨ ((p3 ∧ (((p1 ∧ ((p5 → True) → (p3 → p5))) ∨ p2) ∨ p3)) → ((True ∨ p1) → p5))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587415650020602831725547726 : ((((False ∧ ((False → False) ∧ (False ∧ p2))) → (((p2 ∧ ((p3 ∨ p1) ∨ p4)) ∧ p4) ∨ (False ∨ (True → (p2 ∧ p2))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139861132546109791900085136130 : ((((((((p1 ∨ (p3 ∧ (p1 → p3))) ∨ (p4 ∧ p2)) → p5) ∨ (False ∨ (True ∧ p3))) → False) ∧ p4) ∧ (p5 ∧ True)) → ((p2 ∧ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : ((((p1 ∨ (p3 ∧ (p1 → p3))) ∨ (p4 ∧ p2)) → p5) ∨ (False ∨ (True ∧ p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h18 := h4 h8
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657394288446558231352495769176 : (((((p2 → True) ∧ ((True ∧ (p4 ∧ (p5 ∧ p2))) ∧ (True → ((((((False → p3) ∧ p1) ∨ p3) ∨ False) → p3) ∧ False)))) ∨ (True ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179015792522027046854238297334 : (((p5 ∧ p5) → (((p1 ∧ (p2 ∨ p2)) → p5) → (p4 ∧ (p2 ∨ p5)))) ∨ ((p5 ∨ (False → p1)) ∧ ((p5 → ((p1 → False) → p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343801808486254924926352096108 : (p2 → (p2 ∧ (((((False ∧ (p5 ∨ p1)) → ((False ∨ p3) → p2)) ∨ p5) → ((p5 ∨ True) ∧ ((p1 → p4) ∨ (p5 → (p3 → True))))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69140862022029809683673753961 : ((p5 → (((((p4 ∧ p1) ∨ (p2 ∧ ((p5 ∨ ((False → (p3 ∨ p4)) ∧ (True ∧ p1))) ∨ p3))) → True) → p2) ∨ ((False ∨ p5) → p5))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164791626920847990726076792529 : ((((p5 ∧ (p5 → (p3 → p4))) ∨ ((p4 ∨ p1) → ((False → False) → (False ∨ p1)))) ∨ p3) ∨ (True ∧ (p2 → (p1 ∨ (p1 → (p1 ∨ p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182571527116947231984127081547 : (((((True ∧ True) → False) → (p3 ∧ p5)) ∧ (True ∧ (p4 ∨ True))) ∧ ((True ∧ ((((p2 ∨ p1) → ((p1 ∧ p5) → True)) → p2) ∨ True)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_159265261302524710945651714647 : ((p4 → (((p2 ∨ ((p3 ∧ p2) ∧ ((((p2 ∨ p4) ∧ False) ∨ p4) ∧ p2))) → (False ∨ p5)) ∧ p3)) ∨ (p3 ∨ (((p2 ∨ p5) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_863372877297099429949050916869 : ((((((False ∨ (p2 ∧ (p2 → p1))) ∧ (((False → p1) → (p2 ∧ False)) → p4)) → (p1 ∨ (p1 ∧ (p4 ∧ (p3 → (True ∨ p4)))))) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ (p2 ∧ (p2 → p1))) ∧ (((False → p1) → (p2 ∧ False)) → p4)) → (p1 ∨ (p1 ∧ (p4 ∧ (p3 → (True ∨ p4)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442981773449121939289411028854 : ((((((False ∧ ((p4 ∧ p5) ∨ (p2 ∧ p3))) → (p4 ∨ (False ∨ (False ∨ ((p5 → p4) → p2))))) → (p1 ∧ True)) ∨ (p2 ∨ (False → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53483731920898759478544948123 : (((p3 ∧ ((((p4 → p4) → (False ∨ p5)) → p3) ∧ (False → p2))) → ((False ∧ ((False ∨ p2) ∧ p4)) ∨ (((p5 ∨ p3) ∧ p3) → p3))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178665077454723209301767435139 : ((((p1 ∨ p3) ∨ (p1 ∧ p2)) ∧ ((True ∨ p1) ∧ (p1 → (p2 ∧ p3)))) ∨ (((p4 ∨ (p3 → p2)) ∧ p1) ∨ (p2 → (p2 ∨ (p3 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317957691224150856170170614064 : (p4 ∨ ((p5 ∨ (p1 ∧ (p4 ∨ ((False ∨ (p2 ∧ ((p1 → p5) ∨ True))) ∧ (p1 ∧ (False → (((p3 ∨ (p5 ∧ p1)) → p5) ∧ False))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59214622516383985214436409684 : (((p1 ∨ p4) ∨ (p3 → (p5 ∧ (((p3 ∧ False) ∨ (True ∧ p4)) → ((((p1 ∨ (p1 ∧ p1)) ∧ p2) ∧ (False → p1)) ∧ (p1 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111273367334889367820448833850 : ((((p3 ∧ True) → ((((p1 → (p4 → p1)) ∧ ((p1 → p5) ∧ (p1 ∨ (False ∨ True)))) ∨ (p2 ∧ (p1 → p3))) ∨ p2)) ∧ p4) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179851842519902674816840620372 : (((p4 ∨ ((p3 → (p3 ∨ p3)) → (p5 ∧ ((p1 ∨ p1) ∧ False)))) ∧ p5) → (((p3 ∨ p2) → p2) ∨ (p5 → (p5 → (p1 ∨ (False → p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p3 → (p3 ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347111595759427808150242567644 : (p3 → (((p1 ∨ (p4 ∧ p1)) ∨ ((p1 → (((False ∧ True) ∧ p2) ∨ p5)) ∨ p1)) ∨ ((True → (((p4 ∧ p1) ∧ p1) → (p4 ∨ True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



