variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69036690828584842218020684143 : ((p5 → (((p3 ∧ (((((((False → (p2 ∧ (p5 ∧ p3))) ∨ p2) → True) ∧ p1) ∨ True) ∧ False) ∨ p2)) ∨ ((p3 ∨ True) ∧ p4)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342147835562564281961944468923 : (p2 → ((((True → ((p5 ∧ p2) ∧ (((p3 ∨ ((p2 → p4) ∨ (p3 ∨ p1))) ∧ False) ∧ False))) ∨ p3) → p1) ∨ (p1 → ((p4 → p1) ∨ p1)))) := by
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
theorem thm_5_vars_323217664625230298275652414133 : (p5 ∨ (((((p5 → p4) → ((((p5 ∨ True) ∨ p3) → p5) ∧ p2)) ∧ (p2 ∨ True)) ∨ (((p3 ∨ p4) → p5) → (True ∧ True))) ∨ (True ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_184088631682828185165507879001 : (((((p2 ∨ True) ∧ p1) ∨ (False ∨ (p4 ∨ (False ∧ p1)))) ∨ True) ∨ (False ∨ ((p4 → p5) ∧ (((((True ∧ p3) → p2) → p5) ∨ p3) ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175362391419032064240371485282 : ((p5 ∨ (p2 ∨ (False ∧ (((((p3 → (p5 ∧ p3)) ∨ p4) → p1) ∨ True) ∨ p1)))) → ((((p1 ∧ True) ∧ p4) ∨ p3) → ((True → False) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711469786548584032159000732803 : ((((p5 ∨ (((True ∨ p3) → p4) ∨ p2)) ∧ ((((p2 → (((False → p4) → p5) ∨ p3)) ∨ (True ∧ (p2 ∨ False))) ∧ (p4 ∨ True)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42823073598071295029690854504 : (((p1 → ((p3 ∧ ((True → p4) → p2)) ∧ ((p1 → (((p5 ∧ p1) → True) ∨ False)) → (p3 ∨ (p1 ∧ (p1 ∧ (p4 → p5))))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244384904789310529682662300818 : ((False ∧ p1) ∨ ((p3 ∧ ((p4 ∧ ((((True → (False → p5)) ∨ (p5 → (p4 ∨ p4))) ∨ p1) ∧ ((p4 ∨ p1) ∧ p5))) ∨ p4)) → (False ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h8.left
        let h12 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
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
        -- Conjunctions on the left can always be decomposed.
        let h16 := h8.left
        let h17 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h8.left
      let h22 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354601510333579646493528738846 : (p5 → ((((((((p5 → (p5 ∨ p3)) ∨ (p2 ∨ (p2 ∨ (False ∨ ((True ∨ True) ∨ p4))))) → p1) ∧ (p3 ∨ p2)) → False) ∨ p4) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341669646949711852772335333591 : (p2 → ((((True ∧ (((False ∧ True) → (False ∨ (p5 ∨ ((p3 → (p4 ∨ (p1 → False))) ∨ p5)))) → (p5 → False))) ∨ p1) ∨ p2) ∨ (p1 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319183507354907300405545368328 : (p4 ∨ ((p5 ∧ (((p1 → True) ∧ (((((False ∨ p4) ∨ True) → False) → p4) → p3)) ∧ (p5 ∨ p2))) ∨ ((p1 ∧ p2) → ((p5 ∨ p5) → p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111997953942378729356443809511 : (((((p5 → (False ∧ p5)) ∧ p1) ∨ (((p3 → (p5 ∨ p5)) ∧ (False → (False → (p3 ∨ p1)))) ∧ ((p3 ∨ p5) → p1))) ∨ True) ∨ (False → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351921307675924198067061974028 : (p4 → ((p5 ∨ ((((p3 ∧ (False → True)) ∧ p2) ∨ p5) ∧ p1)) ∨ ((p4 ∨ p3) ∨ (p4 → ((p2 ∧ ((p4 → p4) ∨ (p4 ∨ True))) ∧ p1))))) := by
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
theorem thm_5_vars_337863618237930794048770203732 : (p1 → ((((p4 ∧ (True → p2)) ∨ p3) ∨ (p5 ∧ (((p1 → p5) ∨ False) ∨ False))) ∨ (((True ∧ (((True ∧ False) ∧ p2) ∧ p2)) → p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184799061506178625928173921676 : (((p3 ∧ ((p1 ∨ p1) → p1)) ∨ (p1 ∨ ((p1 → p5) ∧ False))) ∨ ((p2 ∨ p2) → ((p1 → ((True → (p1 ∨ False)) → False)) → (p5 ∨ p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183795857095796362899387173868 : ((((((True ∧ ((p3 ∨ False) ∧ p4)) → p5) → p4) ∨ p2) ∧ False) ∨ (False → (((((p5 → (p2 ∧ False)) → p5) ∧ False) → p4) ∨ (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116523343564065334748810441404 : (((p5 ∧ p4) ∧ (((p3 ∧ (False ∧ ((p4 ∧ p3) ∨ (False ∨ p4)))) ∨ (p4 ∨ ((p5 ∨ ((p1 ∧ p1) → p1)) ∨ True))) → p4)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156701833064944172422520570367 : ((((p4 ∧ (((True → False) ∧ (p2 ∨ p3)) ∨ (True → (p5 → p3)))) → (False ∧ (p3 → False))) ∧ p3) ∨ ((False ∧ ((True → True) → False)) → p4)) := by
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
theorem thm_5_vars_212157927899446340943207029531 : ((True ∨ ((p1 ∨ p3) ∨ p2)) ∧ ((p5 → (p2 ∧ ((p1 → ((True ∧ (p3 → ((p3 ∧ True) ∨ (p5 ∧ p1)))) → False)) ∧ p5))) ∨ (False → p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457225330734910618687454401054 : ((((((((p5 ∧ p2) ∧ (p5 → (p5 → ((True ∨ True) → p2)))) ∨ (p2 ∧ p3)) ∨ True) ∨ p2) ∨ ((((False → False) ∧ p5) → p3) ∨ p3)) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215385136679518139461067176653 : ((p2 ∧ (False ∧ (p4 → p1))) ∨ (((p3 ∨ p1) ∧ ((((p5 → p2) ∧ p4) ∨ p4) ∧ (False ∨ (p1 → (p1 ∧ (p4 ∧ (p3 ∧ True))))))) → p3)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h23 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h24 := h22 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- We need to get the left conjuct of h26 based on <expert-advice>.
        let h27 := h26.left
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h29 =>
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h31 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h32 := h30 h31
        -- We need to get the right conjuct of h32 based on <expert-advice>.
        let h33 := h32.right
        -- We need to get the right conjuct of h33 based on <expert-advice>.
        let h34 := h33.right
        -- We need to get the left conjuct of h34 based on <expert-advice>.
        let h35 := h34.left
        -- One of the premise coincides with the conclusion.
        exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173759381508316366661730017020 : ((((p5 ∨ ((p4 ∧ p3) → p1)) → (p3 ∨ (((False ∧ p4) ∨ p2) ∧ p1))) ∨ p4) → (p3 ∨ (((p3 ∨ p5) ∨ p3) ∨ ((p1 ∧ p4) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41921613401271834400307202445 : ((((p2 ∧ (p3 → p2)) → (False ∨ ((True → ((p2 ∨ ((p5 ∧ ((p2 ∧ (p3 ∧ (p2 ∨ p5))) ∧ p1)) → p4)) → False)) ∨ p3))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736125889049670206803262848609 : ((((False → True) ∧ ((False → p1) → ((p3 ∨ ((p2 → (p3 ∨ p3)) ∧ ((p2 ∨ (p5 ∨ ((p5 ∧ p4) ∧ p5))) → False))) ∧ (True ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139445902849709357317791493362 : ((((((True → p4) ∨ (((p4 → (((p1 ∨ (p1 ∨ (p2 → False))) ∧ p2) ∨ p4)) ∧ False) ∨ True)) ∨ False) ∨ p3) → p1) → (p1 ∨ (False ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True → p4) ∨ (((p4 → (((p1 ∨ (p1 ∨ (p2 → False))) ∧ p2) ∨ p4)) ∧ False) ∨ True)) ∨ False) ∨ p3) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154757700234214698082046587705 : ((((True → p2) → (((p5 → (p3 ∧ p1)) ∧ (p3 ∨ ((False → p1) → p4))) ∨ True)) ∨ (p2 → p5)) ∧ (p1 → (p2 → ((p1 ∧ p3) → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136348319321035832172058985361 : (((p5 ∨ (p2 ∧ (p3 ∨ p2))) ∧ (p4 ∧ ((True → ((p3 ∨ True) ∨ True)) ∧ (((p5 ∨ p2) ∨ (p5 → False)) ∧ False)))) ∨ (p4 → (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299231083497093500938881305603 : (False ∨ (((p5 ∨ (((((((p1 → p4) ∨ p1) → p5) ∧ (p4 ∨ p3)) ∧ p4) ∨ (True ∧ (p4 ∨ (p2 ∨ p4)))) ∧ p1)) → (p5 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663323354283212054583989961123 : (((((False → p4) ∨ ((p2 ∧ (p5 ∨ ((p2 ∨ ((True → ((p5 ∨ ((p1 ∧ p5) ∨ False)) ∨ p5)) ∨ True)) ∧ False))) ∨ p3)) → (p2 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675080494348435867168363038628 : (((((((p1 ∨ (((p4 ∨ (True → p5)) ∨ ((p1 ∧ p2) ∨ p2)) ∧ True)) ∨ (False → p3)) ∧ p1) ∨ p1) ∧ ((p1 ∧ p3) ∨ (True ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657773157815545254576004997169 : ((((True ∧ (((p3 ∨ p5) → (False → p3)) → (((p2 ∧ p1) → (p2 ∨ p5)) ∧ ((p3 ∨ (False → (p4 ∧ True))) ∧ False)))) ∨ (p1 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_227582743178030274143478644165 : ((False ∧ (p1 ∧ p2)) ∨ ((p5 ∨ p5) ∨ ((p2 ∨ (True ∨ p2)) ∨ ((p4 ∧ (p1 ∨ p2)) → (((p5 → False) → (p5 ∨ (p4 ∨ p4))) ∧ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337937552248189863020721708912 : (p1 → ((((p3 ∨ ((p5 → p3) → ((p1 ∨ p5) ∧ p5))) ∧ p4) ∧ True) ∨ ((p5 ∧ p2) → ((p1 → ((False ∨ True) ∧ p1)) ∧ (p1 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712943468382836032344425276077 : ((((False ∧ (p4 ∧ ((p5 ∧ p2) ∨ True))) ∨ ((((False ∧ ((p2 → ((False ∧ p5) ∧ p1)) ∨ p4)) ∨ (p4 → (p2 → p4))) ∨ p5) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172309188397082240430049735122 : ((((True ∨ p4) → (((p4 → p5) ∧ p1) ∨ p4)) → ((p1 → p2) ∨ (True → p4))) ∨ (((True → (p5 ∨ p1)) → ((p1 → True) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55208316377863361985778467669 : ((((p4 ∧ (p3 ∧ p2)) ∧ (p2 ∨ False)) ∨ ((True ∨ p4) ∨ (p1 ∧ (((False ∧ ((((p5 ∨ False) ∧ p4) ∧ False) ∧ True)) ∨ p3) → p3)))) ∨ False) := by
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
theorem thm_5_vars_807601166092067748082662803809 : (((p4 → (((p5 ∨ p5) ∧ (True ∧ False)) ∨ (p2 ∧ ((p4 ∧ (p5 → ((((p3 ∨ True) ∨ p1) ∧ False) ∧ (p2 ∧ p5)))) → (p2 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330372010414775596081836862944 : (True → (p2 ∨ ((((False → (True ∨ (p5 → True))) ∨ (False ∨ (p3 → (((True → (True ∨ p5)) ∨ p3) → p4)))) → p4) ∨ (False ∨ (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260495709520847766936134402065 : ((p3 → False) → (((p3 → p2) → p3) → (p5 ∨ (p4 ∨ (p3 → (((p2 ∧ (False ∨ p1)) ∨ ((p2 → (p3 → False)) ∧ (p3 → False))) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721435411773234506392442350351 : ((((p1 ∧ ((False → p2) → False)) → (p3 → ((True ∧ (p5 ∧ ((False ∧ True) ∨ ((p5 ∨ (p3 ∨ p4)) ∨ p3)))) ∨ (False ∨ (True → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66491255603245116352830277855 : ((True → (((False ∨ (((False → (p3 ∨ p1)) → False) ∨ True)) ∧ (p5 → ((((p1 → (p3 → p3)) ∨ False) ∧ (True ∧ p1)) → p3))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_915115411624590135998898696438 : ((((p3 ∨ (((((p1 ∧ p4) ∨ (p5 ∨ False)) ∨ p1) ∧ ((p1 → p3) ∨ p3)) ∧ p3)) ∧ (p2 ∧ ((True → (True ∧ p1)) ∧ (True ∧ p2)))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h3.left
          let h25 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h3.left
          let h32 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h33 := h32.left
          let h34 := h32.right
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h3.left
            let h41 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- Conjunctions on the left can always be decomposed.
            let h44 := h43.left
            let h45 := h43.right
            -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
            have h46 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h42, we can now drive its conclusion.
            let h47 := h42 h46
            -- We need to get the right conjuct of h47 based on <expert-advice>.
            let h48 := h47.right
            -- One of the premise coincides with the conclusion.
            exact h48
          case inr h49 =>
            -- Conjunctions on the left can always be decomposed.
            let h50 := h3.left
            let h51 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h52 := h51.left
            let h53 := h51.right
            -- Conjunctions on the left can always be decomposed.
            let h54 := h53.left
            let h55 := h53.right
            -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
            have h56 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h52, we can now drive its conclusion.
            let h57 := h52 h56
            -- We need to get the right conjuct of h57 based on <expert-advice>.
            let h58 := h57.right
            -- One of the premise coincides with the conclusion.
            exact h58
        case inr h59 =>
          -- False on the left can always be used.
          apply False.elim h59
    case inr h60 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h61 =>
        -- Conjunctions on the left can always be decomposed.
        let h62 := h3.left
        let h63 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h64 := h63.left
        let h65 := h63.right
        -- Conjunctions on the left can always be decomposed.
        let h66 := h65.left
        let h67 := h65.right
        -- One of the premise coincides with the conclusion.
        exact h60
      case inr h68 =>
        -- Conjunctions on the left can always be decomposed.
        let h69 := h3.left
        let h70 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h71 := h70.left
        let h72 := h70.right
        -- Conjunctions on the left can always be decomposed.
        let h73 := h72.left
        let h74 := h72.right
        -- One of the premise coincides with the conclusion.
        exact h60
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356941010302600470421178370417 : (p5 → (((p3 ∧ p2) ∨ True) ∧ ((p3 ∨ p4) → ((((p2 → False) → (p5 → (p5 ∧ p3))) ∧ (p3 ∨ p4)) ∨ ((False → p2) ∨ (p3 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66703523757249787049888046262 : ((True → ((True ∨ (p5 → p1)) → (False ∧ ((((p3 ∨ ((False ∨ True) ∧ p4)) → p1) ∨ ((p3 ∧ True) ∧ ((p3 → p1) ∨ p3))) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221893593647632005103264997415 : (((p4 ∧ p4) → p4) ∧ ((True ∧ (p3 ∧ ((True ∨ (((True ∧ p1) ∨ p5) ∨ p2)) ∨ p3))) → (p4 ∨ (True → ((p2 → True) ∧ (p2 → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h24
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h25
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h28
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h29
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h30 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h31
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h32
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h33
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49810865692982454104029665441 : (((p1 → (((p2 ∧ (False ∨ p4)) ∧ ((p3 ∧ ((p4 ∨ p4) ∧ (False → p1))) ∧ (False ∧ (p4 → p5)))) ∧ p2)) → ((True → p1) → False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136700050515267403173526483974 : (((False ∧ p5) ∧ ((p3 ∧ (p4 ∧ ((False ∨ p2) → ((True ∨ (p4 ∨ (((p5 ∨ True) ∧ p4) ∨ p4))) → p5)))) ∧ p2)) ∨ ((p1 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110857882005820167293776745560 : (((((((p2 → p5) ∨ (((False → (False → (True → p1))) ∧ (p1 → ((p5 ∧ p2) → False))) ∨ True)) ∧ p2) ∨ p2) → p4) ∧ True) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166285305870370580971836991479 : ((p4 ∧ ((p1 → (p5 ∧ (False ∨ (True → ((p2 ∨ (p1 ∧ (p1 ∨ p4))) ∨ p3))))) → p3)) ∨ (((True ∨ True) → (True ∧ (p1 ∨ True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_46352421580759580128883124448 : ((((((p1 ∨ ((False ∨ p1) → (p3 ∨ p3))) → True) ∨ (False ∨ (True → p5))) → (p5 ∨ (p1 ∨ (p4 → (p4 ∨ p1))))) ∧ (False → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204072837275417827910119849930 : ((p5 → ((p1 → (True ∨ False)) → p5)) ∧ (((((((True ∧ p5) → (p5 ∧ (p4 → (p2 → False)))) → p4) ∧ p5) → True) → (p5 → False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226213229550181126009636203609 : (((p2 ∨ p2) ∨ p5) ∨ (False ∨ ((((p4 ∨ p4) → p5) → (p5 → ((p5 → (False ∨ False)) ∨ (((p2 ∧ False) ∨ True) ∧ p5)))) ∨ (p2 ∧ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328525507856324051482501795608 : (True → ((((p3 ∧ p4) → True) ∧ (p1 ∨ (p3 ∨ (p1 → ((True → (p4 ∨ p5)) ∨ p5))))) ∨ (p3 ∨ ((p2 ∨ (True ∧ (True → p5))) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_474453488603350947486114967522 : (((((p1 ∨ (((p2 ∧ p1) ∨ p4) ∧ (p5 → False))) ∨ True) ∧ ((False → ((p1 → p5) ∨ (p1 → p3))) ∨ ((False ∨ p5) → (False ∨ p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689607753339994498986755191280 : (((((p3 ∧ (((p3 ∨ p1) → p1) ∨ False)) ∨ ((p2 ∨ (p1 ∧ (False ∨ p5))) ∨ p5)) ∨ (True ∨ ((p5 ∨ (False → (p3 → p1))) ∧ p3))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_798352135455261934735702195451 : (((p1 → (((p1 → False) ∧ ((False ∧ (((p4 → (p1 → p4)) → p5) ∨ p1)) ∨ p5)) → ((p1 → ((p2 → (True ∨ False)) → p4)) ∨ False))) ∨ p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774911993075927594119521851072 : (((False ∨ ((p5 ∨ (True ∨ (p3 → p3))) → ((False ∧ (p2 → (p4 ∨ p3))) ∨ ((((False ∧ True) ∧ ((p4 ∧ p1) ∨ p4)) ∧ p2) → p3)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45817825541724347038796599773 : (((p2 → ((((p4 ∨ (p3 → False)) ∧ p4) ∨ (True ∨ (True → ((True ∨ ((p1 ∧ p2) → (False ∨ p2))) ∧ (p3 ∧ p1))))) ∧ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51035054758751093802962458569 : (((True ∨ ((((p5 ∨ ((False ∨ p4) ∧ p3)) → True) ∨ (p5 ∧ (p3 ∨ p1))) ∧ (p3 ∨ p1))) ∧ (p1 ∧ (p4 ∧ ((p3 → p2) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118797106994522786561097953832 : ((True → (((((True ∧ (p2 ∨ p3)) ∨ p5) → (((False ∧ p5) ∧ (True ∨ False)) ∧ (((False → p1) → p3) → p1))) ∧ True) ∧ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172774518040776603493835663112 : (((p3 ∨ True) → ((p5 → ((((False ∨ p1) ∧ False) ∧ (p1 ∧ p1)) ∧ p5)) ∧ p3)) ∨ (((p1 ∨ (p4 ∧ p4)) → (True ∨ p3)) ∨ (p5 ∨ False))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51396069974652811273409271868 : ((((p4 → (((p1 ∧ False) → p2) → ((p2 ∧ (p4 → ((p3 ∨ False) ∨ p1))) ∧ False))) ∨ False) → (((p4 → p1) ∨ (p1 ∨ True)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67767004992196887172698625424 : ((p2 → (((((p2 ∨ (p3 ∨ (p4 → p1))) ∨ p2) ∨ False) → (((p1 ∧ p4) → ((False → (p2 ∨ (True ∨ True))) ∧ False)) ∨ True)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306230833997893726971001771465 : (p1 ∨ (((p3 ∧ p2) → p5) → (p4 ∨ (p1 ∨ (((((p4 → ((False ∧ (p5 ∧ False)) ∨ p1)) → (p5 ∧ p5)) ∨ True) → p5) ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114098577671435291997987124345 : (((p1 ∧ (((False → False) → ((True ∨ (False → p5)) → (p4 ∨ p3))) ∧ (p5 ∧ ((p3 ∧ p4) ∨ p1)))) ∨ (p5 → (False → p3))) ∨ (p1 → p4)) := by
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
theorem thm_5_vars_190884244488935325171984025891 : ((((p1 ∧ p1) → ((p2 → False) → p1)) → (p2 → False)) ∨ ((False ∧ False) ∨ ((p1 ∧ (p3 ∧ False)) ∨ (True ∨ ((p1 ∧ p4) → (p2 ∨ p4)))))) := by
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
theorem thm_5_vars_672571826972562780412485681114 : (((((((True → p1) → (((p2 → p4) ∧ True) ∨ False)) ∧ (((p2 → (p2 ∨ True)) ∨ p2) ∨ p4)) ∧ (p1 ∨ False)) → ((p2 ∧ p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18002057601633656182593626553 : ((((p2 ∨ (p4 → p3)) ∧ (((p1 ∨ p2) ∨ ((True → p4) ∨ (True ∧ ((p1 ∧ p5) ∧ True)))) → p1)) ∨ (((p5 ∨ False) ∨ True) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_251872189819192920060218206975 : ((p3 → p5) ∨ ((p2 ∧ (True → p1)) → ((p5 → (((p4 ∧ False) ∨ p2) → (p3 ∧ p4))) ∨ ((False → p1) ∨ ((True → (True → p2)) ∨ False))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716303241467627289290073146895 : (((((False ∧ p3) ∧ (True ∧ False)) ∧ (((p3 ∧ ((p2 ∨ (p3 ∨ True)) ∨ p2)) ∨ (p1 ∨ p4)) → (((p5 ∨ True) → p5) ∨ (p3 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137966515724744813362805403825 : ((p5 ∨ ((p5 ∨ ((p2 ∧ True) → (p1 ∨ (p3 ∨ (p4 ∨ ((True ∨ p5) ∨ (p1 ∨ p5))))))) ∨ (True ∧ (p4 ∨ p1)))) ∨ (p1 → (p2 ∧ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53269517594403765978341615776 : (((False ∧ ((p2 ∧ (p1 → ((False → (p5 → p3)) ∧ p3))) ∨ p5)) ∨ (((p3 ∧ (p5 ∨ (p5 → (False → (p1 → p1))))) → p1) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198302648477005679423424555016 : ((p1 ∧ ((p3 → (False ∨ (p1 ∨ p3))) → p3)) ∨ (((p5 → False) ∨ ((p3 → True) ∨ (True → ((((p2 → p2) ∧ p4) → p4) → p5)))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308453445991786529972666962617 : (p2 ∨ (((False ∧ ((False → p2) ∧ ((p4 ∧ ((True ∧ (True → True)) → ((p2 ∨ p2) ∧ (p1 ∧ p3)))) ∨ (p3 ∨ p4)))) ∧ (True ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232080989003095540168830851427 : (((p4 ∨ p3) → p2) → ((((((p5 → (p1 ∨ p5)) ∨ (((True ∨ p1) ∨ False) ∧ (p1 ∧ False))) → p1) ∨ p5) ∧ False) ∨ ((p4 → p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134019022909769707205237752241 : (((((((p4 ∨ True) → False) → ((p5 ∧ (p5 → (((p4 ∧ True) ∧ p2) ∧ p2))) → (p1 ∨ p4))) ∧ p5) ∨ p5) ∨ p1) ∨ (True ∧ (p2 ∨ True))) := by
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
theorem thm_5_vars_48951150803771191587289773711 : ((((p5 ∧ (p2 → (True → ((True ∧ ((((p5 ∧ (p3 ∧ p4)) ∧ True) ∨ True) ∧ (p2 ∧ p1))) ∧ p4)))) ∧ p5) ∨ (p4 ∧ (p2 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41219900444444924212612847140 : ((((((p5 ∨ ((p1 ∧ ((p2 → (True → p4)) ∨ p1)) → True)) → (p3 ∧ p3)) ∧ (p3 ∧ p4)) ∧ ((False ∧ p3) ∨ (p2 → p1))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213180598152328070265450652918 : ((((p1 ∨ p4) ∨ False) ∧ p3) ∨ ((p3 ∨ (((p1 → p3) ∧ p3) ∨ (True ∨ (p3 → True)))) ∨ ((p2 ∧ (p3 → ((False ∧ p3) ∨ p5))) → False))) := by
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
theorem thm_5_vars_303089945413984482450649366060 : (False ∨ (p2 → (p4 ∨ ((p5 ∧ (p3 ∧ (p3 ∨ (p4 ∨ (((((p3 → p1) ∧ p3) → p2) ∧ (p4 → p4)) ∧ p1))))) ∨ ((True → False) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697815186237431121756288660989 : ((((p5 → ((((p2 ∨ p1) ∧ p5) ∨ ((p5 ∨ p1) → p3)) ∨ p1)) ∧ ((p4 ∧ ((p4 ∨ (p1 ∧ p4)) → ((p5 ∨ True) → p4))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218945746347808077445300967435 : ((p3 ∧ (p1 → (True ∨ p5))) → (p5 → ((((p1 ∨ ((p3 ∧ ((p1 ∧ (True ∧ False)) ∨ (p3 → (False ∨ p2)))) ∧ p1)) ∨ True) ∨ False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126830864874960698209990901536 : ((p5 ∧ ((((p5 ∧ ((True ∨ p3) → p1)) → (p4 ∧ (p4 ∧ (p2 ∧ p2)))) ∨ p5) ∧ (True → ((p3 ∧ p1) ∨ (p3 ∨ p1))))) → (p1 ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50091984373042258647066595165 : (((p2 ∧ (p2 ∧ ((p4 → (True ∧ (((False → p2) → ((p4 → p3) ∧ p2)) ∧ p4))) ∧ (p5 → p5)))) ∧ ((False ∧ p2) ∨ (p1 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313143182322491728978871910509 : (p3 ∨ ((((p2 → False) → ((p2 ∨ (p2 → (True ∨ (p4 ∧ True)))) ∨ (p5 → (True ∧ p4)))) → ((p3 → (True ∧ (p3 → p4))) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119093844280650028320043552221 : ((p1 → ((p5 ∧ ((False ∧ (True → p3)) ∨ (p4 ∨ p4))) ∧ (p1 ∧ (False ∨ (False ∧ (True → (p1 ∨ ((p5 ∨ p2) ∨ p2)))))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81036769524650224632345159235 : ((((False ∨ (p2 ∧ (False ∨ (True ∧ ((p1 ∨ p4) ∧ p4))))) ∧ (((p4 → (False ∧ False)) ∧ p4) ∧ (p3 → p3))) ∧ (p4 ∧ (p4 ∨ p1))) → p3) := by
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
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h5.left
        let h18 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h3.left
        let h22 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h24 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h25 := h19 h24
          -- We need to get the left conjuct of h25 based on <expert-advice>.
          let h26 := h25.left
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h28 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h29 := h19 h28
          -- We need to get the left conjuct of h29 based on <expert-advice>.
          let h30 := h29.left
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h5.left
        let h33 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h34 := h32.left
        let h35 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h36 := h3.left
        let h37 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h39 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h38
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h40 := h34 h39
          -- We need to get the left conjuct of h40 based on <expert-advice>.
          let h41 := h40.left
          -- False on the left can always be used.
          apply False.elim h41
        case inr h42 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h43 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h36
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h44 := h34 h43
          -- We need to get the left conjuct of h44 based on <expert-advice>.
          let h45 := h44.left
          -- False on the left can always be used.
          apply False.elim h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609363295730850356288661534991 : ((((((p5 ∨ p1) ∨ ((True → p5) ∧ ((False → ((p5 ∨ (((True ∨ p5) ∧ p2) ∧ p5)) ∧ p1)) → (p5 ∨ (p4 ∨ p2))))) ∨ p4) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_45073981248289058501754497886 : ((((False ∧ False) → ((p1 → True) ∧ ((p4 → (p5 ∨ p3)) → ((p5 ∧ (True → (False ∨ (False → (p2 → (p4 ∧ p5)))))) ∧ p4)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50935812342299978920356467518 : (((((((p3 ∨ p3) → p1) ∧ p3) → (p4 → (p1 ∧ p2))) ∧ (False ∧ (p4 ∧ (p2 → p1)))) ∧ (p4 → (False ∧ ((p5 ∧ p2) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614659788209926780598280485335 : ((((((((p4 ∧ ((p4 → (p5 ∨ p1)) ∨ (((p2 ∧ False) → p2) ∨ False))) ∨ p5) → p3) ∧ True) ∨ (p1 ∨ (False ∨ (p3 ∨ p1)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_300228017989597743548044567534 : (False ∨ ((((p3 ∨ (p1 ∨ (p1 → (p1 ∧ False)))) ∧ p4) ∧ (((p4 ∨ ((False ∧ True) ∨ True)) ∨ (p1 ∨ (p5 → p2))) ∧ p2)) → (p5 ∨ p4))) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h3.left
      let h22 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Conjunctions on the left can always be decomposed.
            let h27 := h26.left
            let h28 := h26.right
            -- False on the left can always be used.
            apply False.elim h27
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h3.left
      let h35 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h37
        case inr h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- False on the left can always be used.
            apply False.elim h40
          case inr h42 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
      case inr h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132070854277732963633587103717 : (((p4 ∨ p5) → ((p4 ∨ (((((((True → p5) → p2) ∨ p4) ∨ (p2 ∧ p3)) → False) ∧ True) ∨ p5)) ∨ (p1 → p3))) ∧ (False → (p2 ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165333105550020450859966663285 : ((((((False → p5) → p2) ∨ (False → ((p5 → p2) ∨ True))) → False) ∧ (p1 ∧ (False → p4))) ∨ ((True ∨ (False → (p5 → p2))) → (True ∨ p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62471437721172941973673964999 : ((p3 ∧ ((p3 ∨ p2) ∨ ((p5 ∨ ((p3 → (p4 → p3)) ∧ p5)) ∧ (p3 ∧ (((p1 ∨ (p1 ∧ (p1 ∨ p2))) ∨ (False → p4)) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173968463029320953653740833247 : (((((True → p1) → (p2 → False)) → (p3 ∨ (((p4 ∧ p2) ∧ p5) → True))) → False) → (((((p5 → False) ∨ p3) ∨ p2) → p4) ∧ (True ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (((True → p1) → (p2 → False)) → (p3 ∨ (((p4 ∧ p2) ∧ p5) → True))) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h5
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : (((True → p1) → (p2 → False)) → (p3 ∨ (((p4 ∧ p2) ∧ p5) → True))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h10
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : (((True → p1) → (p2 → False)) → (p3 ∨ (((p4 ∧ p2) ∧ p5) → True))) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h14
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : (((True → p1) → (p2 → False)) → (p3 ∨ (((p4 ∧ p2) ∧ p5) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h18
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171337923437488842418557648201 : (((((True ∧ (((p5 ∧ ((p1 ∨ p1) ∨ p4)) ∨ p4) → p3)) ∨ p2) → False) ∧ p4) ∨ (((True ∨ ((p1 → p5) ∨ p3)) → True) ∨ (p3 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198204718655808095416845333461 : (((p3 → p4) → ((p2 ∨ (p5 ∧ p1)) ∨ p4)) ∨ ((p5 → ((((p3 → True) → (p3 → ((p2 → p1) ∨ False))) → p5) ∧ (True ∨ p1))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158960506923885805085855079549 : ((p2 ∨ (p4 ∨ (((p4 ∧ p5) → (False ∧ (p2 ∧ p3))) ∨ (((p1 ∨ False) ∧ p2) ∨ (p5 ∧ p1))))) ∨ (p3 → (((p4 ∨ p3) ∧ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185461747104219607519563210075 : ((p1 ∨ ((p2 → (((p1 ∧ (p4 ∧ p4)) ∧ True) ∨ p1)) ∨ False)) ∨ ((p2 ∧ (((True ∧ (p2 ∨ (False ∧ p5))) ∨ True) ∨ False)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



