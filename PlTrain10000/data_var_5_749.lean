variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60521429629649625357148586809 : ((True ∧ ((((p1 → ((p1 ∨ True) ∧ p4)) ∧ ((p3 ∨ p2) ∨ (p3 ∧ (p5 ∧ (p5 ∨ (False → (p5 → (False ∨ p5)))))))) ∧ p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611539625580156926772871755318 : (((((p5 ∧ (False → (p1 → ((True → (((True ∧ False) ∨ p2) ∧ p1)) → (True → ((p2 → ((False ∨ p3) ∨ False)) → p5)))))) → p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113304576704537939757524054525 : ((((((p1 ∧ True) ∧ p3) ∨ p5) ∧ (p5 ∨ ((p5 ∧ (p5 → p4)) ∨ ((p2 ∧ (p1 ∨ p4)) → (p3 ∧ p2))))) ∧ (False ∧ p3)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314240459103685221671875498146 : (p3 ∨ (((((False ∧ ((True → False) ∨ p4)) ∨ p3) ∨ ((((True → (False ∧ True)) → p4) ∧ True) ∨ p3)) ∧ (p3 → p3)) ∨ ((p2 ∧ False) → False))) := by
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
theorem thm_5_vars_43164194266741426558804561850 : (((((p4 ∧ (False → True)) ∧ ((((p3 ∨ (p2 ∧ (p1 ∧ False))) ∨ (p2 ∨ ((p2 → p1) → p5))) ∧ p4) ∧ (p3 → p5))) ∧ p2) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187160951425136836372798338178 : (((p4 → False) ∨ (p3 ∨ ((p2 ∨ (p1 ∧ (True ∧ p3))) → p1))) → ((((p2 ∨ True) → True) ∧ (p2 → (((False ∨ p3) ∧ p1) ∧ p3))) ∨ True)) := by
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
theorem thm_5_vars_354673266579017183534488744062 : (p5 → (((p1 → (((((p5 ∨ p3) ∨ (p1 ∨ (True → p4))) ∨ p5) → (((p3 ∨ p5) ∧ True) ∨ ((p4 ∨ p4) ∨ p3))) → p5)) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205609058706785310708764778284 : (((True ∧ p2) ∨ ((p2 → p1) → p5)) ∨ ((True → False) → ((p4 ∨ (p5 ∨ False)) ∧ ((p5 → (False ∧ p5)) ∨ ((p1 ∨ (p2 ∨ p2)) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49579313886803368314230430826 : ((((((p4 ∨ (((True ∨ p2) ∨ ((p4 ∨ p1) ∧ p1)) ∧ False)) ∨ False) ∧ p3) → ((p5 ∨ (True ∨ p2)) ∨ p5)) → (p1 → (p5 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311026401153052161795955534504 : (p2 ∨ ((p1 ∧ False) ∨ (p3 ∨ (((False ∨ (((p5 ∨ p4) ∨ p3) ∧ ((p4 ∨ p4) ∨ (p2 → True)))) ∨ ((p4 ∧ (True ∧ p3)) ∧ p4)) ∨ True)))) := by
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
theorem thm_5_vars_165627845661270664048123418786 : (((((p2 ∨ p1) ∧ True) ∧ (True ∧ p1)) ∧ ((((False → False) ∨ p3) → p3) → (p2 ∨ p5))) ∨ (p3 ∨ (False → ((False → p2) → (p1 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_192921128227138463185084730756 : ((((False ∨ ((p3 ∧ p5) ∨ True)) ∨ False) ∨ (True → p4)) → (((True ∨ False) → ((((p1 ∨ p2) ∧ p1) ∨ (p2 ∨ (p1 → p3))) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625636252923616971888406908605 : ((((p1 → (((p3 → p3) ∧ (((((p2 ∧ False) ∧ ((False → False) ∧ (p1 ∨ p4))) ∧ ((p4 ∧ p3) → True)) ∧ False) → p2)) → p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183780419061468320194593419565 : (((((False ∨ p2) ∧ (((p4 → p4) ∧ p1) ∨ p4)) ∧ True) ∧ p2) ∨ (((((((p1 → p5) ∧ False) ∨ (p2 → p5)) ∨ p5) → True) ∨ p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60462415754713653299605145796 : (((p5 → p2) → (p3 ∨ ((p2 ∧ (p4 ∨ False)) ∨ (p1 ∧ (p5 ∧ (((True ∧ p1) → ((((p3 ∨ p3) ∧ p3) → p3) → False)) ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485575054188707216071105483436 : (((((p2 ∨ ((p2 ∧ p4) ∨ p2)) ∨ p4) ∨ (p3 → (False → ((((p1 → p2) ∨ ((False → ((p4 ∨ p1) → p3)) → False)) ∨ True) → True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721630103062846055188005866278 : ((((p5 ∧ (p2 → (True → False))) → ((((p4 ∨ (p2 ∨ False)) → p2) ∧ (True ∧ False)) ∧ (p2 ∨ ((p2 → (False → p3)) ∧ (p5 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147098130079216326663319910372 : (((((p2 ∨ p1) ∨ p5) ∨ (((p4 ∨ (p1 → p1)) ∨ ((p1 ∨ ((p2 ∧ p5) ∧ p1)) ∧ False)) ∧ p1)) ∧ p2) ∨ ((True → True) ∨ (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40562848184260881352252740481 : ((((p3 → ((p5 ∨ (p4 → (((p1 ∨ ((False → p2) → p1)) → p1) → (p5 → (p2 ∧ (p2 ∨ True)))))) ∧ (True ∨ p2))) ∨ True) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328773725657661514822968719763 : (True → ((True ∨ (p4 ∨ ((p3 ∨ (True → (p5 → p3))) → p5))) ∧ ((p4 ∧ (((p2 ∧ p3) ∨ p5) ∨ (p3 ∧ (p3 ∧ (p4 ∧ p2))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313984886052105966526426844770 : (p3 ∨ (((p4 ∨ (p4 → ((p3 ∨ p4) ∨ False))) → (((p4 ∧ p4) ∧ (((p5 ∧ ((p2 ∧ p2) ∨ p1)) ∨ p5) ∨ False)) → p2)) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152360856442383733510596930224 : ((((p2 ∨ p1) ∨ (p4 → p4)) ∨ (((p4 → p2) ∧ ((p3 → p5) → ((p4 ∧ p4) ∧ (p2 → True)))) ∨ False)) → (((p5 ∨ p4) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308714772894439301454357052764 : (p2 ∨ ((True → (((False ∨ True) ∧ ((True ∧ p1) ∨ (((p1 ∨ (p4 ∨ p2)) → (p4 → (False → p3))) → (p3 ∨ p2)))) ∨ (False → False))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64505960161965981305623681576 : ((p1 ∨ ((p4 ∨ (p4 ∨ ((False ∨ p1) ∧ (p5 ∧ (((p2 ∧ p3) ∧ p5) → p3))))) ∨ ((p1 ∧ (p1 ∧ False)) → (True → (p5 ∧ p4))))) ∨ p3) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670301152172648144056492346448 : ((((((p1 → p3) ∨ p5) ∧ ((((False → (p4 → True)) → (p1 ∨ True)) ∧ p4) ∨ ((False ∨ (p5 ∨ True)) ∧ p1))) ∨ ((False → p2) ∨ p5)) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190645426189587118835045049041 : (((p1 ∨ ((p3 ∨ (False ∧ False)) ∧ (p5 ∨ p5))) → False) ∨ (p4 ∨ (p1 → ((p5 ∨ True) ∨ ((True → (True ∨ p3)) ∧ ((True ∧ p2) → False)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165356865989831952604156054063 : (((p2 ∨ (p2 → (p3 ∨ (((p1 ∧ True) → p2) → (p2 ∧ p5))))) ∧ ((False → p4) ∧ p2)) ∨ (((True → False) → True) ∨ ((p4 → False) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605658423082863191495904296707 : ((((p4 → ((((p2 → (False ∨ (True → p3))) ∨ ((False ∧ (((p4 ∧ p5) ∧ False) ∨ p1)) → False)) → (p2 ∧ p3)) → (p1 ∨ p5))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256977929688191514648352748280 : ((p1 ∨ p5) → ((p4 ∨ p1) → (p3 ∨ (p1 ∨ (((True ∧ ((True ∨ (p4 ∧ p4)) ∧ p2)) → ((False → p1) ∧ p4)) ∧ (True ∨ (p1 → p3))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662862290672142553063171558892 : (((((p3 ∨ (p3 ∨ p1)) ∧ (True ∨ ((p3 → p1) → ((((False ∨ False) ∨ (p2 ∨ (False ∧ (p1 → p5)))) ∧ p4) ∧ p5)))) → (True → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205978915454406855177997163948 : ((p1 ∧ ((False → (p1 ∨ p5)) → False)) ∨ (((p3 → p3) ∧ True) ∧ ((((p1 ∨ p3) → False) → (p4 ∨ (True → p3))) ∨ (False ∨ (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111936774128075900794912853490 : (((((True ∨ p3) → ((p1 ∨ p5) ∧ (False ∨ (False → p5)))) ∨ ((True ∨ p4) ∧ (False → (False → ((p2 ∧ True) ∨ p3))))) ∨ p2) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254376479947122216010557974093 : ((p2 ∧ p4) → (p3 ∨ (((p1 ∧ (p3 ∧ (p1 ∧ True))) ∨ p1) → (((((p3 ∧ p3) ∨ (True ∧ (True → (p3 ∧ p4)))) ∧ p3) ∨ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
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
theorem thm_5_vars_696092013142749125276374151795 : ((((p5 ∧ ((True ∧ ((p1 → ((p4 ∨ p2) ∨ p3)) ∨ p5)) ∨ (p1 ∧ p2))) → (((p4 → p2) → (((p5 ∨ False) → p3) ∨ p1)) ∨ p5)) ∨ p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229174223119943567943763161618 : ((True → (p4 ∨ p2)) ∨ (p2 ∨ ((p1 ∨ (p5 → (p4 ∨ ((p4 → True) ∨ (p2 ∧ (p1 → (((p5 ∨ False) ∧ p2) ∧ (p4 → p2)))))))) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172200495428989470862741304074 : ((((p1 ∨ ((((p1 → p3) ∨ p1) → p1) ∧ True)) → p4) → (True ∧ (True → p5))) ∨ ((p2 → p2) ∨ (True ∨ (((False → p4) → p2) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112010600176866064192293749701 : (((((p5 → p5) ∨ (True ∨ p3)) → ((p1 → (False ∧ (p5 ∧ p2))) → ((True ∧ (((False ∨ False) ∧ p3) ∨ p1)) → p3))) ∨ True) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135578301794511389882126224457 : (((((p4 → False) ∨ ((False ∨ p1) ∨ ((p2 ∨ (p3 ∧ p2)) ∨ (p1 → p1)))) ∨ p4) ∨ (p1 → ((p3 ∨ True) ∧ p1))) ∨ (p4 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165835132961051926598663922317 : ((((p5 ∧ p4) ∧ False) ∨ ((False → p1) → (p4 → ((False ∧ ((True ∧ False) ∧ p1)) ∨ False)))) ∨ ((p3 ∨ (p3 → (p5 ∨ (p1 ∧ p1)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717469370897681175607770920403 : ((((p1 → (True ∧ (p2 ∧ p5))) ∧ (p2 ∨ ((p2 ∨ ((True ∨ p1) ∧ (p1 ∨ False))) → (((((p4 ∨ p5) ∧ p3) ∨ p1) ∨ p4) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219840316818064130693124165244 : ((p3 → ((p2 ∨ p3) → p3)) → ((True ∧ ((p3 ∨ ((True ∨ True) → p5)) ∨ (((((p1 → p5) ∨ (True → p3)) ∧ False) ∨ p1) → True))) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688903684291025931979471491404 : ((((((p3 ∧ p1) ∧ (((p1 ∨ (((False ∨ p2) ∧ p3) ∧ p5)) → p4) → False)) ∧ p2) ∨ ((p1 ∨ (False ∨ False)) ∨ ((p3 ∨ p5) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153437893997592742429016714832 : ((p4 ∨ (((p5 ∨ (p5 ∧ p2)) ∧ ((p5 ∧ ((False ∧ (p3 ∧ p1)) ∨ True)) ∨ (p1 → False))) ∧ (p1 ∧ True))) → ((p2 ∨ p5) ∨ (p1 ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h5.left
          let h17 := h5.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h5.left
        let h20 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- False on the left can always be used.
          apply False.elim h28
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h5.left
          let h32 := h5.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h5.left
        let h35 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157874030253742531948782291759 : (((((p5 ∨ (False ∨ p4)) → (p4 ∨ (p5 ∨ p2))) → p2) ∨ (False ∨ (((p3 → p1) → p5) → p1))) ∨ (((True ∨ False) ∧ False) → (p1 ∨ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111025022315355260746476078523 : ((((((p5 → True) ∧ p4) ∨ ((((False ∨ (p2 → (p5 ∨ False))) ∨ p5) ∨ p5) ∨ (p4 ∧ p1))) → (p2 → (p1 ∨ True))) ∧ p5) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66663037276905914052965811103 : ((True → (((((p3 → p1) ∧ p5) ∧ False) ∨ True) ∧ ((((p1 → p1) → True) ∧ ((((True ∨ p5) ∧ True) ∨ p1) → (p5 ∨ True))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306203479556036555931700827657 : (p1 ∨ ((p4 → (p2 ∧ True)) ∨ (p2 → ((p5 ∨ True) ∧ ((((False → (p2 ∨ p3)) ∨ (True ∧ ((False ∧ p1) → (p5 ∨ p2)))) → p2) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57570933143770805961687974706 : ((((p1 ∨ False) ∧ True) → ((False ∨ (True ∧ p3)) ∨ (p3 → ((p4 → True) → ((p2 → (p3 → (p3 ∨ (p1 ∧ p5)))) ∧ (p2 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172777266203204872642439066504 : (((p3 ∨ p5) → ((((p1 → p2) ∧ True) ∨ p3) → (((p1 ∧ p4) ∨ p3) ∨ True))) ∨ ((False → p3) ∨ ((True ∨ (p3 ∧ p5)) ∧ (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135973875137594030935065173284 : ((((p3 ∨ (True ∧ ((p3 ∨ (p2 ∨ p2)) ∨ p1))) ∧ p4) ∨ ((((p4 → p3) → (p2 ∧ p1)) → (p3 ∧ True)) ∨ p2)) ∨ (p1 ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116150577257756968301081571840 : (((p1 ∨ (p3 ∧ False)) ∧ ((p5 ∧ (p1 → (((False → (True ∧ p5)) ∨ (p5 ∨ ((p3 → p4) → (p4 ∨ p2)))) → p3))) ∨ p2)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62311976367833147676839947157 : ((p3 ∧ (((((p3 → True) ∨ (((((True ∨ False) ∧ ((p5 ∧ True) ∧ p3)) → False) ∧ False) ∧ p4)) → (p1 ∨ False)) → p5) ∨ (p4 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66738332370963331205877825752 : ((True → ((p5 → p3) → (((p4 ∧ ((True ∨ p5) → p5)) ∨ (p2 ∧ (p2 ∨ p1))) → ((p1 ∧ ((p2 ∨ (p2 ∧ p4)) ∨ p5)) ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301354894219093417137749579044 : (False ∨ ((p2 → (p1 → (p5 → p5))) ∧ (((p3 ∧ False) → p3) → (p1 ∨ ((False ∧ ((p2 → ((False ∨ p1) ∨ p3)) ∨ True)) ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763855350570779925713428417496 : (((p3 ∧ (p4 ∨ (((((((p4 ∧ p4) → p3) ∧ (p4 ∧ (p3 → p1))) → (((False ∨ p1) ∧ (p5 → True)) ∧ p1)) → p1) ∧ p2) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351531551157010723373459837422 : (p4 → (((((((p1 ∧ p3) ∨ p1) → p4) ∧ (p5 → p1)) → p3) ∨ ((p5 ∨ p3) → (False ∧ p3))) ∨ (True ∨ ((p2 ∧ (True → p4)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119358134118623150766407081305 : ((p3 → (p1 ∧ ((p3 ∨ False) → (((False → False) ∨ ((p2 → p3) ∧ (p3 ∨ False))) → (p4 ∨ ((p1 ∨ (False ∨ p2)) ∨ p2)))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64779728789211769450805490789 : ((p2 ∨ (((((p1 ∧ p5) ∧ ((p3 → p3) → p5)) ∧ ((p4 ∧ False) → ((p1 ∧ (((p4 → p2) → p5) ∨ True)) → p2))) → p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743079965394351965134097220437 : ((((p4 → p1) ∨ ((((p2 ∧ True) ∨ p1) → (p4 → ((p5 ∧ (p3 ∨ ((False ∧ p2) ∧ p4))) ∨ (p1 ∧ p1)))) ∨ (p1 ∨ (p2 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257450171398219462458131901105 : ((p3 ∨ True) → ((((p4 ∨ (p1 ∨ True)) → ((p5 ∨ False) → (p3 ∧ False))) → p4) ∨ ((False ∧ ((((p1 ∨ True) → p2) ∨ True) → p2)) → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314230169745124010978508924925 : (p3 ∨ ((((((p2 ∨ ((False → p2) → p3)) ∧ p1) ∧ p3) ∨ ((True → ((True ∨ p5) ∧ False)) → (p2 ∨ p4))) ∨ p4) ∨ (p5 ∧ (p2 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312959571206300189162269181358 : (p3 ∨ (((((p1 → (p1 ∧ ((p2 ∨ False) ∧ p2))) ∧ ((((p4 → False) ∨ p3) ∧ (True ∧ p3)) ∨ (True → (True ∧ p1)))) → p5) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54655419027474235791757247563 : ((((((p2 ∨ p2) → p3) → (False ∨ p2)) ∨ p4) → ((p4 ∧ ((((False → p2) ∨ False) ∧ True) ∧ (((p3 ∨ False) ∨ False) → p1))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610822522702376677508948843095 : (((((((((False ∨ p4) ∧ ((True ∧ False) → False)) ∨ p5) ∧ (p3 → (False ∧ True))) ∧ ((False → (p3 ∧ True)) → (p4 ∧ p2))) → p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_330831264622336045821023818603 : (True → (p2 → (p1 → ((p3 ∧ (((True → (((p5 ∧ (True ∨ p4)) ∨ ((p3 ∧ (p3 ∨ p4)) ∨ False)) ∨ (p4 ∨ True))) ∧ False) ∨ p1)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_814481255495624562607529781503 : ((((((((p2 → p5) → (p2 ∨ p5)) → ((p4 → ((False → (True ∧ p2)) ∧ p2)) ∧ (False ∧ p4))) ∨ ((p4 ∨ p3) ∧ False)) ∨ False) ∧ p5) → p3) ∧ True) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : ((p2 → p5) → (p2 ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h6
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159030160497668972321781410448 : ((p4 ∨ (p1 ∧ (((p4 ∧ p1) ∨ p2) → (((p4 ∧ (p4 → (p2 ∧ p3))) ∧ (p5 → p1)) ∨ p3)))) ∨ (p4 → (p5 → ((p4 ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135346555693756725902714232249 : (((p1 ∧ ((p1 ∧ ((p1 ∧ ((p5 → ((True ∧ (True → p1)) ∨ True)) ∧ p5)) ∧ False)) → p1)) ∧ (p2 ∨ (p5 → False))) ∨ (p1 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803289851921733767650976491554 : (((p3 → (((p5 ∧ ((p5 ∨ (p2 → ((((p2 ∧ p3) → False) ∨ p2) ∧ p3))) → True)) → (((p4 → (p1 ∨ p3)) → p4) ∧ p1)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172120123965899647653147266542 : ((((((p3 → ((p5 ∧ p4) ∧ p1)) ∧ p1) ∨ False) → p2) ∧ (True → (False ∨ p4))) ∨ ((False ∨ p4) → (((False ∧ False) ∨ p5) → (p3 → True)))) := by
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
theorem thm_5_vars_632547514086887175764371467118 : (((((p5 ∨ (False ∨ (p4 → ((p5 → (p1 → p4)) ∨ ((((((True ∨ (p5 ∨ p4)) ∧ p5) → p2) ∧ p1) ∨ False) ∨ p3))))) → p4) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77873373388703027431278640065 : (((p1 ∨ (((p5 ∧ ((False → (((p4 → True) ∨ p2) ∨ False)) → ((p2 → (True → p3)) ∧ (p1 ∧ p5)))) ∨ True) ∧ (False → p1))) → False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (((p5 ∧ ((False → (((p4 → True) ∨ p2) ∨ False)) → ((p2 → (True → p3)) ∧ (p1 ∧ p5)))) ∨ True) ∧ (False → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259824734978753697635916504997 : ((p1 → p3) → ((p4 ∨ ((p5 → False) ∨ p1)) ∨ (p5 ∨ ((p5 ∨ ((p2 → p4) → (False → ((p5 ∧ (p2 ∧ p1)) ∧ (p5 → True))))) ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137664933529827759419062264055 : ((False ∨ (False ∨ ((((p2 → p5) ∧ p3) → (True ∧ False)) → (p4 ∧ (p2 ∨ (False ∧ (((p4 ∧ p3) → False) ∧ p2))))))) ∨ (p3 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148662184593754304782946725123 : (((p2 ∨ ((((p2 ∨ True) ∨ True) ∨ p3) ∧ p3)) ∧ ((((p4 → (True ∨ p4)) → False) ∧ True) ∨ (p2 ∨ p1))) ∨ (((p4 ∧ p4) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304072729097753803050131797485 : (p1 ∨ ((p2 ∨ (p1 → (p3 ∨ (False ∨ (((True → ((True → (False ∨ ((p5 → p5) → (True → p4)))) ∨ p3)) ∧ (p4 ∨ p3)) ∨ p1))))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640892267835829716277320317120 : (((((p5 → p1) ∧ ((p3 → ((p2 ∨ False) → (p2 ∨ (((p2 → False) → ((p3 → p1) → p5)) → (False → p2))))) ∧ (p3 ∨ p1))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163424115747590176837805320427 : ((((p2 ∧ p2) → (p2 → p1)) → (((p3 → p2) ∧ True) ∨ (p2 ∨ (False → (True ∨ p3))))) ∧ (p3 → ((p5 ∨ False) → ((p5 → False) → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200457302963563786839176222078 : (((p1 → p4) ∨ ((p2 ∧ False) → (p1 ∨ p2))) → ((True → ((((p4 ∨ ((p1 ∨ p2) → True)) ∧ ((p1 ∧ p5) ∧ p5)) ∨ True) ∨ p5)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161164729735317209508020749748 : (((p3 ∧ False) ∨ ((p4 ∧ p3) ∨ (((p3 ∨ p3) ∧ (p1 ∨ (p1 ∧ p3))) → ((p2 ∨ False) → p1)))) → (((p5 → p5) → False) → (p3 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (p5 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h11
      -- False on the left can always be used.
      apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117017862448550653010553568240 : (((p1 ∨ p3) → ((((False ∨ (p4 ∧ (p5 ∧ (p4 ∧ (p2 ∧ p3))))) ∧ p1) ∧ ((False ∧ p4) → (p2 ∨ p5))) ∨ (True ∨ True))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743473453763337896379745574981 : ((((p5 → p4) ∨ ((((((p4 ∨ True) ∧ p5) ∨ (p1 ∧ ((p2 → p1) ∨ False))) ∧ False) ∨ (p5 ∨ (p1 → True))) ∨ (True ∧ (p5 ∧ False)))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712117740157206551052618487117 : (((((p5 ∨ ((p2 ∨ p2) → p1)) ∨ p1) ∨ ((p3 ∨ (p3 ∧ (True ∨ ((True → (p3 ∧ (p1 ∨ p3))) ∨ ((p1 ∧ p5) ∧ p4))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65568811327228030758757646025 : ((p3 ∨ (p3 → (p3 ∧ ((False ∧ True) ∨ (((True → p3) → (p2 ∨ (p4 ∧ p3))) → ((p1 ∧ p4) ∨ (p5 ∨ ((p3 → p2) ∨ p3)))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121386458184071846890549709559 : (((((((p4 ∧ True) → (p1 ∧ p4)) → (((p1 ∨ (True ∨ True)) → True) → p4)) ∨ (p2 → (p3 ∨ (False → p4)))) ∨ p5) → False) → (True ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 ∧ True) → (p1 ∧ p4)) → (((p1 ∨ (True ∨ True)) → True) → p4)) ∨ (p2 → (p3 ∨ (False → p4)))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205522569964352538689623061893 : (((True ∨ p3) ∧ ((True → p4) ∨ p5)) ∨ (((p3 ∧ ((p5 ∨ True) → (p5 ∧ p1))) ∧ ((p3 → ((p2 → p2) ∧ p3)) ∧ p2)) → (p5 ∨ p4))) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381259041582852945405780560520 : (((((p3 ∨ (((p5 ∨ p3) ∧ ((False ∨ ((True ∧ (((p5 ∨ (False → True)) ∨ p3) ∨ False)) → (p3 ∨ True))) ∧ p5)) ∧ p5)) ∧ True) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_218675506872108254207978610612 : ((True ∧ (p4 ∨ (False → p3))) → (((((p4 ∧ (((p4 ∧ p2) ∧ ((p4 → False) ∧ p3)) ∨ True)) ∨ (p5 → (False → p4))) → p5) ∨ p5) → p5)) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : ((p4 ∧ (((p4 ∧ p2) ∧ ((p4 → False) ∧ p3)) ∨ True)) ∨ (p5 → (False → p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : ((p4 ∧ (((p4 ∧ p2) ∧ ((p4 → False) ∧ p3)) ∨ True)) ∨ (p5 → (False → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h10
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621396539293274985389634445744 : ((((True ∧ (p2 ∨ ((True ∧ ((p4 → p5) ∧ True)) ∨ (p2 ∨ ((p3 ∨ p3) → ((False → (p3 ∧ (p5 ∨ True))) → (p1 ∧ p5))))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186875400429497634652278821759 : ((((True ∧ p4) ∧ (False ∨ False)) → (((True → p2) ∨ p5) ∧ p3)) → (p4 ∨ (False ∨ (p4 ∨ ((True ∨ p4) ∧ (p5 → ((p4 ∨ p3) ∨ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148335288909164028461839426561 : (((((False → p1) → ((p2 → (p4 ∨ (False ∨ (p4 → p1)))) ∧ p5)) → p4) ∧ (((False ∨ p3) ∧ p5) → False)) ∨ (p3 → (False → (p2 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115422640726901379893469628106 : ((((p5 → ((p2 ∨ (p2 → p3)) ∧ p1)) ∧ p3) ∨ ((((p5 → p3) ∨ ((p2 ∧ p2) ∧ (p1 ∧ (p1 ∧ p5)))) → p4) → False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340591347957401538143145837407 : (p2 → ((p2 ∧ ((p2 → p3) → (((p3 ∧ (((False ∨ p2) ∨ p5) → ((p4 → ((p3 ∨ True) → (True → p1))) ∨ p2))) ∨ p5) ∨ True))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661124438308199838089739776756 : ((((((((((p4 ∧ p2) ∨ True) → (False → False)) → (((p5 → (True ∧ p2)) ∨ True) ∧ p1)) → p3) ∧ p2) ∨ (p3 → p4)) → (p4 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799274051396878423906483093269 : (((p1 → (p3 ∧ (p5 ∧ (True → (False ∨ ((((((((p5 → False) ∧ p2) ∨ True) → p4) → False) ∨ p1) ∧ (p4 → p5)) ∨ (p2 ∧ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38860074974230507574784972352 : ((((p4 ∧ (p4 ∧ p2)) ∧ (((p4 ∧ (((p2 ∧ (p1 ∨ p1)) ∧ p5) → p3)) ∧ ((p1 ∧ p5) ∨ ((True ∧ True) ∧ p2))) ∧ p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191516771308246792711245074286 : ((False ∧ ((p2 ∧ p5) ∧ (p2 → (p2 → (p4 → p5))))) ∨ ((True → p4) → (((p5 ∧ True) ∨ p5) → (p4 ∧ (((False → p4) ∨ p5) ∧ True))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655240365682531876491378145725 : ((((((False ∨ (((p4 ∨ (p2 ∧ True)) ∨ p2) → (False ∧ (p2 ∨ (p2 ∨ p3))))) ∧ (p5 → (p4 ∧ False))) ∧ (p1 ∧ p5)) ∨ (p5 → p5)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_301005380243267771157981706552 : (False ∨ ((p5 ∧ (p1 → ((((p4 ∨ p1) ∧ False) ∧ p2) → (p1 → p5)))) → ((((False ∧ (((p5 ∧ p3) → False) ∨ False)) ∧ p2) ∨ p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346638377810434803967283060833 : (p3 → ((p1 ∨ (False ∨ (p5 ∧ (((p2 ∧ p1) → p3) ∧ ((((False ∧ (p3 → p2)) → (p3 ∧ p2)) ∧ p2) ∧ p4))))) ∨ ((p2 → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



