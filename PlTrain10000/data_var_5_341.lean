variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38593586050245370955128000508 : ((((p2 ∨ (p5 ∨ ((p3 ∨ ((p4 → p5) ∨ p4)) → p5))) → (((p2 ∨ p2) ∨ p2) → (p5 ∧ ((p1 → (p1 ∧ False)) ∧ p3)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165668500227237402619715719638 : (((p3 ∨ (False ∧ ((p2 ∨ p5) ∨ p4))) ∨ (((p3 ∨ (True ∨ (p2 ∧ p1))) ∧ True) ∨ p1)) ∨ ((True ∧ (p4 → (p5 → False))) → (p2 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_705238894234269630383864788905 : (((((p3 ∧ (p5 → ((p4 ∧ p5) → True))) ∧ p1) ∧ ((False ∧ (p3 ∧ ((p2 → (p5 ∨ (False → (p1 ∨ False)))) ∧ True))) ∧ (p3 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308679419395150378212812665124 : (p2 ∨ ((False ∨ (((((p4 ∨ (p1 ∧ p4)) ∧ True) ∨ (True ∨ ((p2 ∨ p5) → (p2 ∨ (p1 → p2))))) ∨ (p5 ∨ (False ∧ p4))) ∧ True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_624482457365833677228817448228 : ((((p4 ∨ (((p3 ∨ p3) ∧ (((False ∧ (((False → ((True ∧ p1) → p3)) ∨ True) → False)) → ((p3 ∨ p4) ∧ p2)) ∧ p4)) ∧ p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_305552239401941550874310091299 : (p1 ∨ (((p2 ∨ (False → (True → (False ∨ ((p4 ∧ p2) → False))))) ∨ p5) ∧ (((False ∨ p4) ∨ True) ∧ ((p5 ∨ p3) ∨ (False → (False ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201022523027043187311374353821 : ((p4 ∨ ((((p3 → True) ∧ p3) ∧ False) ∨ True)) → (((((((p4 ∧ True) → p3) ∧ (p2 ∨ True)) ∧ p4) → False) → (p5 ∧ p4)) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258050422126640618670644972213 : ((p4 ∨ p2) → ((((p2 ∨ (p5 → (((p5 ∧ ((p3 → p2) ∧ ((True ∨ p1) ∨ p2))) ∧ p3) ∧ p5))) ∧ p1) ∨ p1) ∨ ((p2 ∧ p4) → p4))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608402609752762125603723443862 : ((((((p5 → (((True ∧ (p3 → p3)) ∧ ((((p3 ∨ p5) → p2) → p4) → p4)) ∨ ((False → (p2 ∨ p1)) → p3))) ∨ p3) ∨ True) ∨ False) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_355857479892820939454480775656 : (p5 → (((p2 ∧ (((((True ∨ (p4 ∨ p2)) ∧ (False → p5)) ∧ p2) → p5) ∨ p1)) → (p5 ∧ ((p4 ∨ p3) ∧ p2))) ∨ (False → (False ∧ p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165416016390436750011701780005 : (((((p3 → p2) ∨ (p1 ∧ (True → (False ∨ True)))) ∧ (p1 ∨ p3)) → ((True → p2) ∧ p1)) ∨ (False ∨ (p4 → ((False ∧ (p2 ∨ p4)) ∨ True)))) := by
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
theorem thm_5_vars_40512021481275630574377839624 : ((((p3 ∧ ((p2 ∨ (p1 ∧ (((p5 ∧ (p5 → (True → p4))) ∧ p1) ∧ p5))) → ((((p1 → p3) → p2) ∨ p2) ∨ p3))) ∨ p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346778831207670924466525531919 : (p3 → ((((p4 ∧ (p4 ∨ p5)) → (((False ∧ (p1 ∨ p4)) ∧ (p2 ∨ False)) ∨ p3)) ∧ ((p4 ∧ False) ∧ True)) ∨ (False → (p4 ∧ (p2 → p4))))) := by
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
theorem thm_5_vars_735328200752060947859787703240 : ((((p4 ∨ False) ∧ ((((p5 ∧ (p1 → (False ∨ (p4 ∨ p5)))) ∨ ((True → p1) ∨ p2)) ∨ p5) ∨ (True ∨ ((p1 → p5) ∧ (True → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118561239256247128053411792414 : ((p4 ∨ (((p3 ∨ (((((p3 → ((p1 → ((p4 → p2) ∨ p5)) ∨ p5)) ∧ p4) → (True ∨ False)) ∧ p1) ∨ p1)) ∧ p1) ∧ p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301779592497885544301336685217 : (False ∨ ((p1 ∧ True) ∨ (p4 → ((((p5 ∨ ((p3 → p1) → p5)) ∨ ((p2 ∨ p4) ∧ p3)) → False) ∨ ((True ∨ (p5 ∧ False)) ∨ (p2 → False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246618141022176920963909896261 : ((p5 ∧ p3) ∨ (((p3 ∨ ((((((p3 ∨ p4) ∧ p5) ∧ (p2 → (p2 ∨ (False ∧ (False → p1))))) → p1) ∨ False) ∧ False)) ∨ (True → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140263032592933938019432028717 : ((((True ∧ (((p1 → False) ∧ (((False → p3) ∧ (False → p3)) ∨ False)) ∧ (p1 → p5))) ∨ p4) ∧ (p2 ∨ (p5 ∧ p4))) → (p1 → (p4 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h15 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h17 := h10 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h39 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h40 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h41 := h34 h40
        -- False on the left can always be used.
        apply False.elim h41
      case inr h42 =>
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- One of the premise coincides with the conclusion.
        exact h44
    case inr h45 =>
      -- False on the left can always be used.
      apply False.elim h45
  case inr h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h47 =>
      -- One of the premise coincides with the conclusion.
      exact h46
    case inr h48 =>
      -- Conjunctions on the left can always be decomposed.
      let h49 := h48.left
      let h50 := h48.right
      -- One of the premise coincides with the conclusion.
      exact h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341880261650788674512113857207 : (p2 → ((p4 ∨ (p5 ∨ (True ∧ ((False ∧ (p5 ∨ True)) → (p3 ∧ ((((p4 ∧ (p5 ∨ False)) → (p1 ∧ True)) ∧ p3) ∨ p2)))))) → (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855575301646467017621800145736 : ((((((p2 → ((False ∧ (p5 → False)) ∧ (p1 ∨ (p5 ∧ ((False ∨ ((p3 ∨ True) → True)) ∨ (p3 → (p5 ∧ p1))))))) ∧ p2) ∨ True) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → ((False ∧ (p5 → False)) ∧ (p1 ∨ (p5 ∧ ((False ∨ ((p3 ∨ True) → True)) ∨ (p3 → (p5 ∧ p1))))))) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183858595996800481368681159966 : ((((((p2 → False) ∨ p4) → False) ∧ ((True ∧ p5) ∧ p1)) ∧ p5) ∨ (((p4 ∧ (False → False)) → p1) → (((False ∧ p4) → (p3 ∧ p2)) ∨ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338256053009577307318757520127 : (p1 → ((p3 → (((p2 ∧ p3) → p2) ∧ p2)) ∨ ((((((p1 ∧ p5) ∧ (((True → False) → p4) → p2)) → (p5 ∧ p1)) → p5) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147780282987084379904458448062 : ((((False ∧ p4) → (((((True ∧ True) ∧ ((p1 → p2) ∨ (True ∧ p4))) ∨ p5) ∨ (False ∨ p3)) ∨ False)) → p5) ∨ (((True ∧ p2) ∧ p5) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165378607069144127820145978399 : ((((True ∧ ((p4 ∧ False) ∨ (True ∧ (False → p2)))) → (True → False)) ∨ ((p1 ∨ p2) → False)) ∨ (((p4 → (p3 ∧ p2)) ∨ False) → (p1 ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198330313206179640216812868246 : ((p2 ∧ ((p1 ∨ ((True → False) ∧ False)) ∧ p3)) ∨ (((True → p1) ∧ p4) → ((p3 ∨ (p1 → False)) ∨ (p4 ∧ ((p3 ∨ (p2 ∧ p5)) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699822978602693276283915288011 : ((((((p3 ∧ (p5 ∧ p4)) ∧ (p4 ∨ (p5 ∨ p5))) → (True ∧ p3)) → (((((((p3 → True) → p1) → p5) ∧ p2) ∨ p4) ∧ p4) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_708855945268322695441724609805 : ((((((p3 ∧ p1) → (p1 → p4)) ∧ (p2 ∧ True)) → (((p2 → p3) → ((p4 ∧ ((((p4 → p2) → p1) ∨ p3) ∨ p4)) ∧ p2)) ∨ p2)) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175069891469468633008730661316 : ((p3 ∧ (((((True → p3) → ((True → p1) → p2)) → (p5 → p1)) ∧ p4) ∨ False)) → (((p5 ∨ True) → True) → (True → ((p1 ∧ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114721458792553740563008343900 : (((((((((True → p2) → p4) ∧ p5) ∨ (p3 ∧ p4)) ∨ p5) → p5) → (True → p1)) → ((p3 ∨ (p1 → p1)) → (p2 → p2))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351237185369569557730255734136 : (p4 → (((((((p4 → (p4 → p4)) ∧ p1) ∧ False) ∧ True) ∨ p3) ∨ (p1 ∧ (p5 ∨ (p3 ∧ (p2 ∨ (p3 → p5)))))) ∨ (p4 ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307140915066405438482143586578 : (p1 ∨ (False ∨ (((p3 ∨ ((p2 ∧ p5) ∧ (p3 ∨ (False ∨ (p2 ∨ (p5 → p5)))))) → p1) ∨ (p3 ∨ ((False → (p2 ∨ (p4 ∨ p2))) ∨ True))))) := by
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
theorem thm_5_vars_158435577417262306248208583147 : (((p1 ∨ False) ∨ ((False ∧ p4) ∨ ((((False → p1) ∧ (p2 ∧ ((True → p4) ∧ p5))) ∨ p5) → p4))) ∨ ((p1 ∧ False) → (False ∧ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198597595443604011202823362796 : ((p2 ∨ ((((p4 → True) ∨ p3) ∧ True) → p2)) ∨ ((True → (False ∧ (p1 ∧ (p1 ∨ (True → p2))))) → ((True ∨ (False → (p2 → p5))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345459660298897016037529942442 : (p3 → (((True ∧ ((p1 ∧ ((p2 → (False ∧ (p1 → p4))) → ((p2 → ((True ∧ (p5 → p2)) → True)) → p1))) → p3)) → (p1 ∨ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726878822099044138964429178 : ((((p5 ∨ p1) ∧ ((p2 → True) → False)) → (((p4 ∧ ((p3 ∨ p5) ∧ ((p3 ∧ p4) ∨ (False ∨ p4)))) ∨ False) → (False ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41989787948897428084053516910 : ((((p5 ∨ p4) ∧ (((((p5 ∨ False) ∧ ((p1 → ((p3 ∨ True) → (p5 → p2))) ∧ p3)) → p2) → ((p5 ∨ p2) ∨ p4)) ∧ p3)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313327991190244285790616716914 : (p3 ∨ ((p4 ∨ ((((p5 ∧ p1) ∧ False) ∨ p3) ∨ (((p1 → p1) ∧ ((True ∨ (p1 → (True ∨ (True ∧ (p4 → p4))))) ∧ True)) ∨ p2))) ∨ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119268919421350966843109129582 : ((p3 → (((((p5 ∧ p5) ∨ ((p5 ∨ p5) ∧ ((False ∨ (p1 → p3)) → (p5 ∧ ((p5 ∨ p3) ∨ p1))))) ∧ True) ∧ p4) ∧ p4)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54240377063256548974737000766 : (((((True ∨ (p4 ∧ p5)) ∧ p5) ∧ (False → False)) ∧ ((p4 ∨ (p4 ∨ (False ∧ (((p3 ∨ ((p4 ∨ True) ∧ p4)) → p1) ∧ p3)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230961220658926532369608087363 : (((p4 ∧ False) ∨ p1) → (((p2 ∨ ((((p4 ∧ True) ∧ (p5 → p4)) ∨ (p3 → p5)) → p2)) ∧ (p3 ∨ p1)) ∨ (p2 ∨ (p3 ∨ (p1 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147643858583914128378954785998 : ((((p2 ∨ ((((p2 → p3) ∧ ((False → True) ∧ False)) ∨ p2) ∧ (False ∨ ((p5 ∨ False) ∨ False)))) → p3) → p2) ∨ ((True → (p1 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767568175203710804446875558619 : (((p5 ∧ ((((p5 → (p2 ∨ (((p2 ∨ ((p3 ∨ p3) ∧ (p1 → p3))) ∨ p5) ∧ p4))) ∧ p3) ∨ ((p3 ∨ p3) ∧ (p3 ∨ p1))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704739737495883901082232478818 : ((((p3 ∧ ((p2 ∨ ((p2 ∧ p4) ∧ p5)) ∧ (p5 ∨ p1))) → (((p2 ∧ (p4 ∨ (False ∧ p4))) ∨ (p5 → (p1 → False))) ∨ (p2 ∨ p3))) ∨ p5) ∧ True) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53893973494143411213913085892 : (((p1 ∧ ((False ∨ ((p5 ∨ p1) ∧ (p2 ∨ p1))) ∨ p2)) ∨ ((True ∧ ((p1 ∨ False) → ((True ∧ (p5 ∨ p1)) → (p1 → True)))) ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209002666478842303936168828171 : ((False ∨ (((p4 ∨ p2) ∨ True) → p5)) → ((((p1 ∨ ((p4 → p2) ∧ p1)) ∨ p4) → (((p2 ∧ True) ∨ (p2 → p5)) ∨ (False → True))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645975171129719644120696235027 : ((((True → (((((p5 ∨ p3) ∨ (p5 → (p1 ∨ (p2 ∨ p4)))) ∨ True) ∨ p3) ∧ ((True ∨ p4) ∧ (((p1 ∧ p5) ∨ p3) ∧ False)))) → p4) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118728790305795246660469654488 : ((p5 ∨ (((((p4 → p2) ∧ (p1 ∧ (False → (p2 ∨ (p3 ∨ p2))))) ∧ (p4 → True)) ∧ True) → ((p2 → (p2 ∧ p5)) ∧ True))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260951459658541625606485923399 : ((p4 → p1) → (((True → (p1 → (((p1 → True) ∨ p1) → p3))) ∨ ((p1 ∨ True) → ((p4 ∧ (p5 ∧ p1)) ∨ ((p5 ∨ p4) → p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351402408791824168317534808635 : (p4 → (((((((False → ((p5 ∨ True) → p1)) → p2) ∨ True) ∧ p4) ∧ (p1 ∧ p1)) ∨ ((p1 → False) ∧ True)) ∨ (((True ∨ p1) → p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316461165287605117739763297068 : (p3 ∨ (p1 ∨ ((p5 ∨ p2) ∨ (True ∧ ((False ∨ ((((False → (p2 → (p1 → p4))) → p1) ∧ (p1 → True)) → True)) ∨ ((p1 → p4) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615536832698994274427138485027 : ((((((((True ∧ p2) → p3) ∧ True) ∧ ((p1 → p5) → (p2 → (p5 ∧ (p2 ∨ p2))))) → ((p4 ∧ p3) → ((p2 → p1) ∧ p2))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117007474031429260549928434448 : (((False ∨ p3) → (True ∧ ((True → (True ∨ ((False ∨ (p4 ∧ p5)) ∧ (((False → True) ∧ False) ∨ p2)))) → ((False ∨ p5) ∨ p5)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322774959280583523409795202077 : (p5 ∨ ((((((p2 → p2) → p4) ∧ ((False ∧ (p4 → p5)) ∨ ((True ∨ p2) → p1))) ∧ (p1 → (p3 → True))) ∧ ((p3 ∨ p5) ∨ p1)) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h14 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h15 := h11 h14
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h17 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h18 := h11 h17
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263409330549947929775838888720 : (True ∧ (((p1 → (True → p1)) → (((((p2 → p2) ∨ ((False → p1) → (False ∧ (p4 ∨ p4)))) ∧ p3) ∧ False) ∨ p5)) ∨ (False → (p3 ∧ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234114786393285306770388388667 : ((True → (p1 ∨ False)) → ((p5 ∧ (p2 ∨ (((False → p4) ∧ (p2 ∨ p4)) → (((p3 → ((p2 → p3) → (p4 ∨ p1))) ∧ p5) ∨ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608594282919419764041129008121 : (((((((((False → ((p2 ∧ ((p3 ∨ False) ∨ (False → p5))) ∧ ((p3 ∨ p4) → p2))) → p3) ∨ p5) → p3) ∧ (p5 ∨ p4)) ∨ p1) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_694793173594318313744240063269 : ((((True → (((True ∨ False) → (p5 ∨ p3)) → (p5 ∧ ((p4 → False) → p1)))) ∨ ((False → ((p4 ∨ (p1 → p5)) ∧ (p2 ∨ p1))) ∨ p4)) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299326190383655714768051416021 : (False ∨ (((p4 ∧ (p1 ∨ (p5 ∧ p4))) ∧ ((False ∧ p1) ∨ (p5 → (((p3 → (False ∨ p1)) ∧ p1) ∨ ((False → p2) ∨ (p1 ∧ False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46268100005313414191525176342 : ((((True → (((p1 → ((p2 → (True ∧ True)) → (p4 ∧ p1))) ∧ p5) → (p1 → ((False ∨ False) ∨ p1)))) → (p5 → p4)) ∧ (False → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162531422479666738069979693753 : (((p3 → ((((False ∨ ((p1 → (p2 ∧ p3)) → p1)) ∨ (False → p5)) → False) → False)) ∨ p3) ∧ ((p4 ∧ True) → ((False → (p5 → p5)) ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ ((p1 → (p2 ∧ p3)) → p1)) ∨ (False → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148779377690082968615118039241 : ((((True ∧ False) ∧ ((p5 ∧ p2) ∧ p5)) ∨ ((p5 ∨ p3) ∧ ((((False ∨ p1) ∨ p2) ∨ False) ∨ (p2 ∨ False)))) ∨ ((False ∨ True) ∨ (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41793439650418856442839397791 : (((((False → True) ∨ (p1 ∧ p2)) → (p1 ∧ ((p4 ∧ (True ∧ ((((p1 → p4) → p5) → (p2 → p4)) ∧ (p3 → p5)))) → p2))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116559474908914173835072460601 : (((p2 ∨ True) ∧ ((p2 → ((True ∧ ((p3 ∧ True) ∨ (p5 → p3))) ∨ ((p2 ∧ p2) ∧ ((p5 ∧ p5) ∧ (p3 ∧ p2))))) ∨ True)) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_255164834121159201617239999332 : ((p4 ∧ p3) → (p2 ∨ ((((True → True) → (False ∧ p3)) ∨ (((p5 → p2) ∧ p1) → (((p4 ∧ ((p1 ∧ True) → True)) → False) ∨ p4))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110824060053253115843966214642 : (((((p4 → p3) ∧ (p3 ∨ ((((False → (p4 ∧ True)) ∧ p2) ∨ ((((p2 ∨ True) → p1) ∨ False) → p1)) ∨ p1))) ∨ p4) ∧ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149996794478283015911457536145 : ((p4 ∨ (p2 → (False ∨ (p4 ∨ (((p2 ∨ False) → (((p5 ∧ (p2 ∨ (p2 ∧ p4))) ∨ False) ∨ p2)) ∧ True))))) ∨ ((p1 ∨ (False ∧ p3)) ∨ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655999409260529499577999510616 : ((((((((p4 ∧ False) → p3) ∧ True) → ((p5 → p5) → (((p4 ∧ p3) ∨ p2) ∧ p1))) ∨ (p4 ∧ (True ∧ (p4 ∧ p5)))) ∨ (p3 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225059922309964441305463888842 : (((p1 ∧ False) ∧ p5) ∨ (((p2 ∧ (((((False ∧ p4) ∨ False) → (True ∧ (((p5 ∨ p3) → False) ∨ p3))) ∨ p1) ∧ True)) ∨ (p1 → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908242121795802586534803082217 : ((((p5 → ((p3 ∨ p3) ∨ (((p2 → ((p5 ∨ False) ∧ (p2 ∨ p1))) ∨ (p1 ∧ p4)) ∧ (True ∧ True)))) → ((p5 ∧ (p1 ∧ p3)) ∧ p2)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → ((p3 ∨ p3) ∨ (((p2 → ((p5 ∨ False) ∧ (p2 ∨ p1))) ∨ (p1 ∧ p4)) ∧ (True ∧ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619201743185237263516444119924 : (((((p1 → (p3 ∨ p5)) ∨ (p4 ∨ (False ∨ ((p3 → ((True → p5) → (((True ∧ False) → p2) → (p5 → (p2 ∨ True))))) → p1)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86036530698512520770027208210 : ((((p1 → True) → ((p4 ∨ (True ∨ (True ∨ p5))) → False)) ∧ (p4 → ((False → ((True ∧ p1) ∨ (True ∧ p3))) ∨ (p3 ∧ (p5 ∨ p2))))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ (True ∨ (True ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701292778205599956253447220427 : (((((((p5 ∨ p1) ∧ False) ∨ (p5 ∨ p4)) → (p2 ∧ p2)) ∧ ((((p5 → (p4 ∧ p2)) → (p4 ∧ (p4 ∧ False))) → (p5 ∧ True)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115449974102340735160478164679 : (((((p2 ∨ False) ∧ True) → (p3 ∧ (p3 ∨ p3))) ∨ (((False → (False ∧ (p3 ∧ (True ∨ (p4 ∨ True))))) ∨ (True ∨ p3)) → p2)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339777244759428039453556870238 : (p1 → (p4 ∨ (p5 → ((((False ∧ p3) → False) ∨ p1) ∧ ((p1 → (p4 ∨ ((p1 ∧ False) ∨ (False ∨ ((p3 ∨ p5) ∨ (p4 → p2)))))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198475491844466934425420602580 : ((p5 ∧ (p4 → (True ∧ ((False ∧ True) → True)))) ∨ ((((False ∨ (False → p2)) ∧ p1) → ((p5 ∨ p3) ∨ p5)) ∨ ((p4 → p4) ∧ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157732989211835107044353106180 : (((True → ((((p1 ∨ p1) ∧ ((p3 → p3) ∧ p4)) → False) ∧ (p5 ∨ p1))) → (p1 ∨ (p1 ∨ p2))) ∨ ((False ∧ ((False ∨ p2) ∧ False)) → p4)) := by
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
theorem thm_5_vars_88934236386989862788731229636 : (((True → (p4 ∨ (False → p2))) → ((p5 ∧ (((p5 → (p1 → ((p5 → p5) → False))) ∨ (p1 ∨ p2)) ∧ p4)) ∧ ((False ∧ p3) ∧ p3))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (p4 ∨ (False → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61953446494998232351957039547 : ((p2 ∧ (((p4 → ((((False ∧ (False ∨ p3)) ∧ p1) ∨ (p5 ∧ p5)) ∨ p4)) → p2) ∨ ((False → False) ∧ (((p5 → p5) ∨ True) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336242425529047412274201330979 : (p1 → (((((p2 ∧ p1) ∨ p4) ∨ (p2 ∨ ((p5 → (p2 → ((p4 → True) → p4))) ∧ (p5 ∧ p3)))) ∨ ((True ∨ p3) → (p3 → True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_432319859698978451162575692975 : ((((True → (((p4 ∨ p5) ∨ ((False ∨ p5) ∨ False)) ∧ (((False ∧ p5) → (p2 → (p2 ∧ (p3 → (p1 ∨ p4))))) ∧ p5))) ∨ (False → p1)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_682935917495030158526654083213 : (((((p5 ∧ False) ∨ (p2 ∧ (p2 ∨ (((p3 ∨ (p2 ∨ p1)) ∨ p5) ∨ ((False ∧ p1) → p2))))) ∧ (True → (p3 ∨ (False → (p3 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197029997124504185723486083121 : (((((p1 ∨ p1) → p2) → (p5 ∨ p4)) ∨ p4) ∨ (p4 → (((((p2 ∧ False) ∨ False) ∨ (True ∧ p1)) ∨ p1) → (True ∧ ((p5 → True) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316729575190073621075480853355 : (p3 ∨ (True → ((((True ∨ p5) ∧ (((p2 → p2) ∨ (False ∨ True)) ∧ ((((p4 → p2) ∧ p2) ∧ p1) ∧ (True ∧ (p5 → p3))))) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173894599411011701976624746606 : ((((True → ((p3 ∨ ((p4 → p1) → p1)) ∧ ((p3 ∧ p3) ∧ p2))) ∨ p2) → True) → (((p2 → (p3 ∧ p5)) ∨ (p3 → p3)) ∨ (p3 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339819179722766091923100961757 : (p1 → (p5 ∨ ((p3 ∨ p3) ∨ (((False ∧ p4) ∧ p4) ∨ ((True ∨ p1) ∨ (((False ∧ p3) → (p3 ∨ (p5 ∨ (p2 ∧ (p5 → p1))))) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_193729707109086399358314059003 : ((p2 ∧ (p3 ∧ (((p2 ∨ (False ∨ True)) ∧ p3) ∨ p3))) → ((p2 ∧ (p3 ∧ False)) ∨ (((True ∨ (p3 ∨ p5)) → (p2 ∧ p5)) ∨ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214458147509151795897174344978 : (((True ∧ False) ∧ (p2 ∧ p1)) ∨ ((((((True ∧ ((p1 ∨ p3) ∨ p1)) ∨ (p5 → p1)) ∨ p2) ∧ (p2 ∧ p1)) ∧ (p4 ∧ p4)) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134388258055816232482684426746 : (((p5 ∨ (((p4 ∨ ((p2 → (False ∧ False)) ∨ (p4 ∧ p1))) ∨ (p3 ∨ (p2 → p5))) ∧ ((p5 ∨ p2) ∧ p3))) ∨ True) ∨ (p2 ∧ (p3 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249585216511142696341971456899 : ((p5 ∨ p2) ∨ (p4 → (((p4 ∨ (p2 → (p2 ∧ p3))) → (False ∨ (p5 ∧ False))) ∨ ((p1 ∧ ((p3 → (p2 ∨ p4)) ∧ (p3 ∧ p1))) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330282654068259924111228533445 : (True → (False ∨ (p5 ∨ ((p1 ∨ (p4 ∨ p2)) ∨ ((((False ∨ p5) → p2) ∨ True) → (((((p3 ∨ False) ∧ p1) ∨ p3) ∧ False) → (p5 ∨ p3))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173888639518479463268434231538 : (((((p1 → p3) ∧ ((((True → (True → True)) → p1) ∨ False) ∨ p1)) ∨ p5) → False) → (((p5 → (p3 ∧ p3)) ∨ p1) ∨ ((True ∨ p1) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 → p3) ∧ ((((True → (True → True)) → p1) ∨ False) ∨ p1)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 → p3) ∧ ((((True → (True → True)) → p1) ∨ False) ∨ p1)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264816841816075606710548849302 : (True ∧ ((p4 ∧ p5) ∨ (p5 ∨ ((p5 ∧ p5) ∨ ((False ∨ (p4 ∧ False)) ∨ ((False → ((p1 ∨ ((p4 ∧ (p4 ∨ p2)) ∧ p2)) → True)) ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206278516968274988374253930054 : ((False ∨ (p2 ∨ ((p1 ∨ False) ∨ p2))) ∨ ((((p1 ∨ ((((False → p3) → (p2 ∧ p3)) ∧ p1) → p4)) → p2) ∨ p3) → (False → (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258798111115192802750392631561 : ((True → False) → ((p2 ∨ p3) ∨ ((p4 ∨ (True ∧ ((p5 ∧ (p3 ∨ (p2 → p4))) → (((p5 ∧ p1) → (p2 ∨ p1)) ∨ True)))) ∧ (p1 ∧ p4)))) := by
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
theorem thm_5_vars_254187738100819075042105615548 : ((p2 ∧ p1) → (p2 ∧ (((p4 ∨ (p5 → p5)) ∨ (p4 ∨ ((((p3 → p4) ∨ p2) ∨ ((p5 ∨ p2) ∨ p3)) ∨ p3))) → (p2 ∧ (p3 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Conjunctions on the left can always be decomposed.
            let h20 := h1.left
            let h21 := h1.right
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h1.left
            let h24 := h1.right
            -- One of the premise coincides with the conclusion.
            exact h23
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h27 =>
              -- Conjunctions on the left can always be decomposed.
              let h28 := h1.left
              let h29 := h1.right
              -- One of the premise coincides with the conclusion.
              exact h28
            case inr h30 =>
              -- Conjunctions on the left can always be decomposed.
              let h31 := h1.left
              let h32 := h1.right
              -- One of the premise coincides with the conclusion.
              exact h31
          case inr h33 =>
            -- Conjunctions on the left can always be decomposed.
            let h34 := h1.left
            let h35 := h1.right
            -- One of the premise coincides with the conclusion.
            exact h34
      case inr h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h1.left
        let h38 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h37
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h1.left
      let h42 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h41
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h1.left
      let h45 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h44
  case inr h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h1.left
      let h49 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h48
    case inr h50 =>
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h51 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- Disjunctions on the left can always be decomposed.
          cases h52
          case inl h53 =>
            -- Conjunctions on the left can always be decomposed.
            let h54 := h1.left
            let h55 := h1.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h54
          case inr h56 =>
            -- Conjunctions on the left can always be decomposed.
            let h57 := h1.left
            let h58 := h1.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h57
        case inr h59 =>
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h60 =>
            -- Disjunctions on the left can always be decomposed.
            cases h60
            case inl h61 =>
              -- Conjunctions on the left can always be decomposed.
              let h62 := h1.left
              let h63 := h1.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h62
            case inr h64 =>
              -- Conjunctions on the left can always be decomposed.
              let h65 := h1.left
              let h66 := h1.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h65
          case inr h67 =>
            -- Conjunctions on the left can always be decomposed.
            let h68 := h1.left
            let h69 := h1.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h67
      case inr h70 =>
        -- Conjunctions on the left can always be decomposed.
        let h71 := h1.left
        let h72 := h1.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h70



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304691548169079315459976312469 : (p1 ∨ (((False ∧ (((p4 → p3) ∧ ((((p3 → p4) → ((((True → p4) ∨ p5) → p3) ∧ p5)) ∧ p1) ∧ p2)) ∧ p1)) ∨ True) ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199065940525743259470190172694 : (((((p4 → (False ∨ p3)) ∧ False) → p4) ∧ p5) → (p4 → ((((p5 ∧ False) → (((p1 ∧ p4) → p4) ∨ (p1 → p1))) → p2) ∨ (p4 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252142914284368438379125368592 : ((p4 → p3) ∨ (((((p5 ∧ (p3 ∨ ((p1 ∨ (p4 ∧ p2)) ∧ ((True ∨ p4) ∧ True)))) → p4) ∨ ((p5 ∧ p2) ∨ (p1 → p4))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149115609942900035276925888910 : (((False ∧ True) ∧ ((p3 ∧ (p2 → ((p1 ∨ (p3 ∧ (p3 ∧ (p4 ∧ False)))) ∨ ((False → p3) ∨ False)))) ∧ p4)) ∨ ((p1 ∧ p5) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314920004452073098586675705769 : (p3 ∨ (((p4 → (((p4 ∧ p4) ∧ (True ∨ False)) ∧ p2)) → p5) ∨ (((p1 ∨ (p1 ∨ (True → False))) ∨ ((True → False) ∨ p1)) ∨ (True → True)))) := by
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



