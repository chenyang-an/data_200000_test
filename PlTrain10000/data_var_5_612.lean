variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117109275628186072134209899715 : (((p2 → p5) → (((((p1 ∨ ((p3 → True) ∧ p5)) ∨ ((p5 ∨ p4) → (p1 ∨ False))) ∧ True) ∨ p5) ∨ ((p1 ∧ p1) → p1))) ∨ (p3 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_64496369064013959642234294126 : ((p1 ∨ (((((False → ((p4 ∧ (p1 ∧ p4)) ∧ ((p2 ∨ p1) ∧ p4))) → True) ∧ p2) ∧ True) → (False ∧ (False ∧ (False → (p3 ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745354095580844040323879309806 : ((((p5 ∧ p3) → (((p4 ∧ p2) → ((((((p5 → True) ∨ p4) ∧ False) → ((p1 ∨ ((p4 → True) ∨ p1)) ∨ True)) → p1) ∨ p4)) ∨ False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142334362520114956159996161390 : ((p3 ∧ ((p5 → (p4 ∧ (p5 → (((p4 → ((True ∨ p4) ∧ p1)) ∧ p1) ∨ p5)))) → (((p4 ∧ p4) ∨ p5) ∧ p2))) → ((p1 → p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219428206146298375642483010116 : ((p4 ∨ ((p1 ∧ p1) ∨ p5)) → ((p1 ∨ (p5 → p3)) → ((((True → p2) ∨ False) ∧ ((p5 → p1) ∨ p3)) ∨ (((p3 ∧ p1) → p3) ∨ p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h26
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194258023929457186519249745287 : ((p5 → (((p2 ∧ (p3 ∧ (p3 → p5))) ∧ p1) ∧ p4)) → ((p2 ∨ ((p1 → p4) → p4)) ∨ (True → ((p5 ∨ True) ∨ ((p3 ∨ p3) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41437324616332856747941233718 : (((((p1 → (p4 ∨ True)) ∨ ((p4 ∧ p5) ∨ ((p1 ∧ (p2 → p2)) ∧ p5))) → ((p5 ∧ p2) → ((p4 ∧ (p1 ∨ True)) → p1))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137921464865064865010474453210 : ((p4 ∨ ((p1 → p2) → ((p3 → False) ∧ (((p3 ∨ ((True ∧ (p1 → (p2 ∨ False))) → p4)) ∨ p2) → (False ∨ p5))))) ∨ (False → (p1 ∧ p1))) := by
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
theorem thm_5_vars_702595942321465315220912360217 : (((((p3 ∧ ((((p1 → p4) ∨ p2) ∧ True) ∨ p4)) → p2) ∨ (((True ∨ p5) ∨ (True ∨ (p2 ∧ ((p5 → p1) ∨ p2)))) ∨ (p5 → p3))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67933758585147165769742045978 : ((p2 → ((False ∧ ((p2 ∧ p4) ∨ ((p5 ∨ p3) → True))) ∨ ((True ∧ (p1 ∧ (p4 ∨ p4))) ∨ ((p5 ∧ ((p3 ∨ p5) ∨ p2)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54528757394577766234443034228 : ((((p1 ∨ p5) ∨ (p4 ∧ ((p2 → False) ∨ p4))) ∨ (((p3 ∨ (True ∨ p1)) ∨ False) ∧ (((p3 ∨ p1) ∨ (p4 ∧ p1)) → (p4 ∨ True)))) ∨ p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788265827284423363468006034642 : (((p5 ∨ ((p1 → ((((p4 ∧ ((False ∨ (p5 ∧ p2)) ∨ p2)) ∧ (p2 ∨ (p4 ∨ (p4 → (p4 → p4))))) ∧ (p5 ∧ p4)) ∨ True)) ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195827280529847535606690610566 : (((p5 ∨ p3) → ((p4 ∨ True) ∨ (True ∨ p1))) ∧ (p4 ∨ (True ∧ ((((p1 ∨ p1) ∧ False) ∨ (True ∨ False)) → ((p3 → (p5 ∧ p4)) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166572199148892236931037389089 : ((True → (((p2 → ((p5 → (p3 → p5)) ∨ ((p2 ∧ (False ∧ p4)) ∧ p5))) → p3) ∨ True)) ∨ (True ∨ (p1 → (False ∧ (p1 → (p4 → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138554712877514500844065918229 : ((((p2 → (((p5 ∧ (p2 ∧ p2)) ∧ p1) ∧ ((p4 → (p5 → True)) ∧ (True → (p2 ∨ (p1 ∨ p5)))))) ∨ p2) ∧ p3) → ((p1 ∨ p1) → p1)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245050988481747438114619969715 : ((p1 ∧ p5) ∨ ((((p5 ∨ ((p2 ∨ p1) → p1)) → False) ∨ ((False → p5) → ((p3 → False) ∨ (p1 → ((True → False) → p2))))) ∨ (False ∧ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55003792780243097966121953615 : ((((p3 ∧ p1) → (p3 ∧ (False → p4))) ∧ ((((p5 ∨ ((True → (((p2 → False) ∨ p2) ∧ False)) ∧ p2)) ∨ p3) → p5) → (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134617749555265647921335939178 : ((((True → (p5 ∧ (p4 ∨ (p3 ∧ (((p4 ∨ p5) ∨ (True → p5)) ∨ (p1 ∧ p3)))))) ∨ (p1 → (p1 ∧ p5))) → p1) ∨ (p3 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675879232421148032369569080905 : ((((((True → (p2 ∧ (p3 ∧ p1))) ∧ (((p3 → p4) ∧ True) ∨ p2)) → (p5 ∧ ((p5 ∧ p3) ∨ p2))) ∧ (((p2 → p3) ∨ False) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615676560665364461914174030661 : ((((((p1 ∧ (p1 ∧ (p1 ∨ (p5 ∧ (False ∨ (False ∧ p1)))))) ∨ (p2 → True)) ∧ ((p1 → p1) ∨ (p2 → ((p1 ∨ p1) ∨ True)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66049768076177963420877424462 : ((p5 ∨ ((((p5 → (((((p2 ∨ p5) → False) → (((p2 ∧ (False ∨ False)) → False) ∧ (True → p2))) → p1) → False)) ∧ False) ∨ p3) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64069052813427525356039753082 : ((False ∨ (((((True ∧ (False ∧ p3)) ∨ p1) ∨ (False ∧ (True ∨ False))) ∧ ((p5 → p5) → p1)) ∨ (p5 ∨ ((p5 ∧ p5) ∨ (p3 → True))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67441230983729890020284275061 : ((p1 → ((((True → (p4 ∧ ((p1 → ((True ∧ p1) → ((False ∨ p1) → False))) → p2))) ∧ p1) → (False ∨ False)) ∨ ((False → p5) ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52526804408803105457949966044 : (((((p5 → (((p4 ∨ True) ∧ ((False ∨ p4) → p3)) ∧ p3)) → p1) ∨ p1) ∨ (True ∨ ((p2 ∨ False) ∧ (p3 → (False ∧ (p4 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160192705194440664971931014231 : (((True → (p4 ∧ (p2 → ((False → (p1 → (p3 → (True → (p2 ∨ p4))))) ∧ p5)))) ∧ (p5 ∨ p2)) → (p5 ∧ (((p1 ∧ False) ∧ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
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
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h17 := h12 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192920534359485903606771693861 : ((((p3 ∧ (p2 ∨ (False ∨ True))) ∨ p4) ∨ (p3 ∧ p3)) → ((p2 → True) → (((p2 ∨ p1) ∧ ((p2 → (p3 → True)) ∧ (p2 → False))) → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h14 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h15 := h8 h14
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h19 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h6
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h20 := h8 h19
            -- False on the left can always be used.
            apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h22 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h23 := h8 h22
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h27 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h28 := h8 h27
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h5.left
    let h31 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h37 =>
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h38 =>
            -- False on the left can always be used.
            apply False.elim h38
          case inr h39 =>
            -- One of the premise coincides with the conclusion.
            exact h29
      case inr h40 =>
        -- One of the premise coincides with the conclusion.
        exact h29
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48563600358489359756434294704 : ((((((p2 ∧ ((p4 → True) → True)) ∧ p2) → (False ∧ (p3 ∧ (False ∨ (p2 ∨ (False → (p2 ∧ p3))))))) → False) ∧ (p5 ∧ (p1 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_79088518015070745474048610756 : (((True → ((((p2 ∧ True) ∧ (True ∧ (((p5 ∨ p5) ∧ True) ∧ (p5 ∨ p2)))) → p2) ∧ (p2 ∧ (p3 ∧ (p3 ∧ False))))) ∧ (p5 ∨ p4)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766272970985157426470992285890 : (((p4 ∧ ((p5 → p3) ∨ ((p4 → p1) ∨ (((p2 → p1) → ((True ∨ ((True ∧ (p2 ∧ p2)) ∧ p5)) ∧ False)) ∧ ((p1 ∧ False) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39346321130765044617246023194 : (((p2 ∧ (p1 ∨ ((p5 ∨ (((p2 → p3) ∧ p4) ∧ ((True ∧ ((p1 ∨ p5) → ((p1 → p4) → p1))) ∧ (False → p4)))) ∨ False))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300055241970067059859115946732 : (False ∨ (((((True ∨ (p3 ∨ (False ∨ p1))) ∨ p5) ∧ ((((p4 ∧ False) ∨ (p4 ∧ (p1 → False))) → (True ∧ p1)) ∧ p5)) ∧ p3) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656978316395014397208947878804 : ((((((p2 → False) ∨ (p3 ∨ p3)) → (p4 → (((p3 ∧ p3) ∧ p1) ∨ (p4 ∨ ((p3 ∧ True) → ((p3 ∨ p4) ∨ False)))))) ∨ (p4 ∨ p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443517446090330135470718711751 : (((((False ∨ (p2 ∨ (p5 → ((p2 → p4) ∨ p3)))) ∨ (((p3 → p2) ∧ ((True ∨ (p5 → p1)) ∧ p5)) ∨ p2)) ∨ (p5 → (p2 → p5))) ∧ True) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138299479895519000771352660663 : ((p3 → ((((False ∧ p2) ∧ p4) ∨ ((p5 ∨ (p4 ∧ p4)) ∨ ((True ∧ True) ∨ True))) ∨ ((p2 ∧ True) ∧ (p5 ∨ p4)))) ∨ ((True ∧ p4) ∧ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161253172833914151904746028636 : (((True ∨ p4) → ((p4 ∧ ((p4 ∨ False) ∨ (p1 ∧ (p2 ∧ (p1 ∧ (p3 ∧ False)))))) ∧ (False ∧ p2))) → ((p2 → (p3 ∧ False)) ∧ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111488058339650526281438340496 : (((p2 → (p4 ∨ ((p1 ∨ (p5 ∨ (p1 ∧ ((False → (p5 → p4)) ∧ (p4 → ((True ∧ True) → (p1 ∨ True))))))) ∧ p4))) ∧ p4) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119572889495236712225582299352 : ((p5 → (((p3 ∧ (p2 ∧ False)) ∧ p2) ∨ (((((((p2 → p4) ∨ p5) ∨ False) ∧ False) → p3) ∧ p2) ∧ ((p5 → p4) → False)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172535624104971511176251915895 : (((p3 → (p3 ∨ True)) ∧ ((True → False) ∧ ((((p1 ∨ p1) ∨ p5) → True) ∧ p3))) ∨ (p2 ∨ ((p3 → (False ∨ ((p1 ∧ False) ∨ True))) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135891170351043179872146810316 : (((p5 → (((p2 ∨ (p5 ∨ p5)) → p1) ∧ ((False → p4) → p5))) ∨ (((p3 ∧ (False ∨ (True ∧ p3))) ∧ False) ∧ p3)) ∨ (p2 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725346192223334349837474710762 : ((((p4 → (p3 ∧ p1)) ∧ (p1 ∨ ((((p5 ∧ (((((True → p3) ∨ False) ∧ p4) ∧ (True → True)) ∨ (p5 → p4))) ∨ p2) → p1) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134644029758260996209213360171 : (((((p3 ∨ (p4 ∨ p4)) ∨ (p1 → (p5 → ((p5 ∧ p3) ∧ p2)))) ∧ (True → (p5 → ((True ∨ p5) ∨ p2)))) → p2) ∨ (p4 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942016142744996986452088082276 : ((((((p2 ∧ p3) → p5) ∧ p5) ∧ (False → (p5 ∧ ((p5 → True) ∧ (((True ∨ ((p3 ∨ (p2 → False)) ∧ (p1 → p5))) ∧ False) ∨ p4))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178054016467309264434514073144 : ((((p2 → (((False → p3) ∨ p1) ∧ ((False → p4) ∨ False))) ∧ p1) → False) ∨ (((p1 ∨ ((False ∧ True) ∨ p2)) ∧ (p5 ∧ p5)) → (p2 ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323511219469408250997650788227 : (p5 ∨ (((p3 ∧ p3) ∨ (((p1 ∨ ((False ∨ (p5 ∨ True)) ∧ (False → ((p5 ∧ False) → p4)))) ∨ (p3 ∨ p2)) ∨ p5)) ∨ (p4 ∧ (True ∧ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135091131857782632550316645322 : ((((False ∧ ((((True ∧ p1) → p3) ∧ (p1 ∨ False)) ∨ False)) ∨ (p2 ∨ ((p1 ∧ p1) ∨ (p4 → p4)))) ∨ (p1 ∧ p4)) ∨ ((p1 ∨ p1) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69023706266710712654892738618 : ((p5 → ((((p1 ∧ (p5 → False)) ∧ (((False → ((p5 ∨ p5) → p1)) → (p2 ∧ p1)) ∧ (p1 ∧ ((p4 ∧ p4) ∨ False)))) ∧ False) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47547076664174192473629921785 : (((p5 ∨ (p5 ∧ (((p3 ∨ p3) → ((((p3 ∧ p2) ∨ p3) ∧ p5) → p3)) ∧ (p3 ∨ ((p3 ∧ True) ∧ (p5 ∧ False)))))) ∨ (False → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198369261607434039476905087575 : ((p3 ∧ (((p3 → (p4 → p4)) ∧ p5) ∨ p5)) ∨ ((p3 → p1) → (((p4 ∨ (((True ∧ p2) ∧ (p5 → p1)) → False)) → p1) ∨ (p2 → p2)))) := by
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
theorem thm_5_vars_341116226382099486239255979462 : (p2 → (((((p1 ∨ True) → (((False → ((p3 → (p4 → (((False ∧ True) ∧ p5) ∨ (False → p2)))) ∨ p5)) ∧ p1) ∧ False)) ∧ p3) ∧ p3) → p5)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58925459486227262670691778492 : (((p1 ∧ p2) ∨ (((p4 ∧ (p1 ∧ (p1 ∨ p2))) ∨ True) ∨ (p3 ∨ (((p4 → p5) ∧ p3) → (False ∧ (((p2 ∨ p1) ∧ p4) → p4)))))) ∨ p5) := by
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
theorem thm_5_vars_329518294639041013343546053224 : (True → ((p1 ∧ False) ∨ (((p4 ∧ False) ∧ ((p2 ∨ (True → False)) ∧ (False ∧ p4))) ∨ ((True ∨ (p1 → (False → ((p2 → p3) ∨ p5)))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_188283725091519035683190410706 : (((p3 ∨ ((False ∧ p1) ∨ (p4 ∨ (True ∨ p5)))) ∨ p4) ∧ (p4 ∨ (False → ((p2 ∧ (False ∨ (p3 ∧ (((p2 → p2) → True) ∧ p5)))) ∧ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190200692295952440479423897873 : (((p4 ∨ ((p2 ∧ (p1 ∧ (p2 → p4))) ∧ p2)) ∧ p3) ∨ ((False ∧ (p5 ∧ p1)) → ((True ∨ ((((p5 ∨ p1) ∨ p2) → p5) → p5)) ∨ False))) := by
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
theorem thm_5_vars_135929431686867133216880374968 : (((p2 → ((p1 → ((p2 ∨ p5) ∧ ((False ∧ p4) ∨ p2))) → p4)) → (True ∧ (((p4 ∧ p3) ∨ False) ∨ (p4 ∨ p3)))) ∨ ((p4 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173226875861483389181086592154 : ((True → ((p5 ∧ ((p1 ∧ (((True ∧ p4) ∧ (True → True)) → p1)) ∧ p2)) ∧ p3)) ∨ (((p4 → (p3 ∨ p5)) ∨ (p1 → (False ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622025065944435535906808111429 : ((((p2 ∧ ((((p1 ∧ p4) ∧ (False ∨ (p4 → (p2 → False)))) → (p1 → ((p4 ∧ ((p1 ∧ (p3 ∧ p1)) → p3)) ∧ p3))) ∨ p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50857372672375980536651341439 : (((((((p3 → p1) ∨ False) ∨ (True ∨ ((p3 ∨ False) → (p5 ∨ False)))) → (p4 ∨ False)) ∨ True) ∧ ((((p4 → True) ∨ False) ∨ p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669620866786573362912833243746 : (((((((((p2 ∧ False) → p3) ∧ (p5 → (False ∧ p5))) → (True ∨ p5)) → (False ∧ p2)) ∨ (p4 → (p3 → True))) ∨ (p1 ∧ (p2 ∨ p3))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962025049883911650473835133030 : ((((p4 ∨ p4) ∧ ((True ∨ p5) → ((p3 ∨ True) → (p4 ∧ ((True ∨ ((((p5 → (p1 → p1)) → False) ∨ (False ∧ False)) ∧ True)) ∧ p1))))) → p1) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164818891048442850658437713147 : ((((p4 ∨ p5) ∨ ((p2 → (p4 ∧ ((p3 ∨ p3) ∧ ((p1 → p1) ∨ p1)))) ∨ p4)) ∨ True) ∨ (p4 → (p5 ∧ (p1 → (p3 ∨ (p4 → p5)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184045162968756242200221548913 : ((((((p3 ∨ p2) ∨ (p3 → p4)) ∧ p3) ∧ (p3 ∧ p2)) ∨ True) ∨ (((p3 ∨ p4) → (((((p2 ∨ p3) ∧ p4) ∧ True) → False) ∨ p5)) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162181537133949008913179793487 : ((((((((p3 → p3) ∧ p3) → p5) ∨ (p4 ∧ p4)) ∨ p4) → ((p3 ∧ p2) ∨ True)) ∧ True) ∧ (((p5 → p1) ∨ (p4 ∧ (p5 ∧ True))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314644113622071018231797523788 : (p3 ∨ (((p3 → ((False ∧ ((p5 ∨ p2) ∧ p1)) ∨ ((p3 ∨ p5) → (p2 → p1)))) ∨ True) ∨ ((True ∧ (False ∨ ((p2 ∧ p3) ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118313076996681975160283068027 : ((p1 ∨ (p5 ∨ (p2 → (((p1 → p1) → False) → (((p2 → p5) → (p5 → (p3 → (True → ((False ∧ p2) ∨ False))))) ∨ True))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172280192765930125361128639548 : (((p1 ∧ ((False ∧ (p4 ∨ (p2 ∨ True))) ∨ p1)) ∨ (((True → True) ∨ p4) → False)) ∨ (((p1 ∨ p4) → (p2 ∧ (p4 → p5))) → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350148044136751173850099931009 : (p4 → ((((False ∧ ((p2 ∧ p2) ∧ (p5 ∧ (p3 ∨ p4)))) → p5) ∧ ((p5 ∧ False) ∨ (p2 ∨ (p1 → ((p3 ∧ (p4 → True)) ∨ False))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191142199745435036097406648708 : ((((p4 ∧ p1) ∨ p2) ∨ ((p5 ∨ (p5 ∧ p1)) ∧ p1)) ∨ ((p5 → ((False ∧ True) → p1)) → ((True ∧ (False → ((p2 ∧ p1) ∨ p1))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45791645423345246777476549208 : (((p1 → ((True → (((False ∧ (p3 ∧ p1)) ∧ ((p2 ∧ p4) ∨ p3)) → ((False ∧ (p2 ∨ False)) ∨ True))) ∨ ((True → p5) → False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677158142009363472384132221323 : (((((((p1 ∧ False) ∨ (((((False ∧ p4) ∨ (p3 → (p1 → p5))) ∧ p4) ∨ p2) ∨ False)) ∧ p1) ∧ p4) ∨ ((p1 ∧ p4) → (False → p4))) ∨ False) ∧ True) := by
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
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134671633019723691742669840046 : (((((p2 ∧ ((p3 ∨ (p5 ∧ True)) ∧ p4)) ∧ p5) ∨ (False ∨ ((p1 ∨ (((True ∨ p3) ∧ p1) ∧ False)) → True))) → p5) ∨ (p2 → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258774586799878572708833241417 : ((True → False) → (((p5 ∨ True) → (p1 ∧ ((p3 ∨ (((p2 → (False → ((p5 ∧ (p4 ∧ p3)) ∨ p5))) ∧ p1) ∧ p5)) ∨ p3))) ∧ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h16
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245376195501311044679893960457 : ((p2 ∧ p3) ∨ ((False ∧ p5) ∨ ((((False → ((True ∨ (p1 → p3)) ∨ True)) ∨ (((p2 → (p1 ∧ False)) ∨ p1) ∨ p1)) ∧ (p2 ∨ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47826394035644065076190229547 : ((((((True ∧ p1) ∨ True) ∧ (((p1 → (p5 ∧ p3)) ∧ ((p5 ∧ ((p5 → p4) ∨ (False ∨ p3))) → p2)) ∧ p2)) → p5) → (p2 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22048210959174958521271937265 : ((((p4 ∧ (((True ∧ p4) ∨ p5) → p3)) ∧ False) ∨ (((p1 ∧ (p5 → p4)) ∨ ((p4 ∧ (False ∨ (p2 ∧ True))) ∧ p3)) ∨ (p5 → p5))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301598346442433627757832293029 : (False ∨ (((True ∨ p3) ∨ True) → ((True → (False ∧ (False ∨ (p1 → (p5 ∨ (p4 ∧ True)))))) → ((p4 ∧ p3) ∨ (p2 ∧ ((False ∨ p4) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- We need to get the left conjuct of h6 based on <expert-advice>.
      let h7 := h6.left
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47782890187675196739348436630 : (((((((p3 ∨ p5) ∨ ((p4 ∧ ((((p3 → (p1 ∨ p4)) ∨ p2) → p4) → True)) ∧ True)) ∧ (p4 ∨ True)) ∧ p4) → True) → (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323481404194258092935557274848 : (p5 ∨ ((((((p4 ∨ (p2 ∨ p5)) ∧ ((((p2 → p5) ∧ p4) ∨ (p1 → False)) → p1)) → p1) ∨ (False ∧ p2)) → p4) ∨ ((False → p2) ∨ p5))) := by
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
theorem thm_5_vars_652619216792111420968894891512 : ((((False ∨ (p3 ∧ ((False ∧ p5) ∨ (((((p1 → p2) ∨ p4) ∧ p4) → p4) ∨ (p1 ∧ (((p1 → False) ∧ p5) ∧ p5)))))) ∧ (p3 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51964529099001547357276984008 : (((((True ∨ False) → p5) ∧ (((((p2 ∧ (p5 ∨ False)) ∧ p3) ∧ p3) ∧ p1) ∧ p1)) ∨ (((True ∧ ((p2 → False) → p3)) ∨ p3) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262335563543200672427739387948 : (True ∧ ((((((True → p3) → True) ∨ p4) ∨ False) → ((((p5 ∨ p1) ∧ (p4 ∨ p4)) → p4) → (((p2 ∧ p3) ∧ (False → p2)) ∨ True))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261336780471660385780335672453 : ((p5 → False) → (((((p3 ∨ p3) ∨ p5) ∧ (((p5 → p3) → True) → p4)) ∧ True) ∨ (p5 → ((((p4 ∧ p2) → True) → True) ∨ (p2 → p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653043349639632751229769865484 : ((((True → ((p2 → ((True ∧ ((((p5 ∨ p3) ∧ p3) ∧ (False → (p3 ∨ (p1 ∧ (False → p1))))) ∧ p3)) ∨ p5)) → False)) ∧ (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111783778117236406338536815938 : (((((((p1 → ((False ∧ False) → (False → (p4 → p4)))) → (False ∨ p5)) ∨ True) ∧ ((False → p3) ∨ p2)) ∨ (p1 ∨ False)) ∨ p3) ∨ (p5 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326972825981610338029377262182 : (True → ((((True → ((((p3 → (p2 → ((p5 ∨ (False ∧ True)) ∨ p1))) ∧ p3) ∧ p3) → p2)) → (p2 ∧ p5)) ∧ (p3 → (False ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247793657817075272471124466371 : ((p1 ∨ p1) ∨ ((((p3 ∨ ((p4 ∧ (p3 ∧ (p3 → p4))) ∨ p5)) ∧ p3) ∨ True) ∧ ((((p2 ∨ (True ∧ p5)) ∧ (p2 ∧ p3)) → p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158525314458324788904217653948 : (((p5 ∨ True) → (False ∨ ((False ∨ ((False ∨ p5) ∨ (p3 ∧ (p2 → (p1 ∨ False))))) ∨ (p4 ∨ p2)))) ∨ (False → (p2 → (p3 ∧ (True ∧ p1))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226757662474217675592658445586 : (((p2 ∧ p1) → p4) ∨ ((((p1 ∨ p1) ∨ False) ∧ p1) ∨ ((p2 ∧ (True → p4)) → (((p5 ∨ False) ∨ (p3 ∨ p5)) ∨ (True ∨ (p3 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62896891595303108319821530231 : ((p4 ∧ ((p4 ∨ False) ∨ ((((p4 ∧ True) ∨ p2) ∨ ((((p1 ∨ p4) → True) → False) ∧ (p5 ∧ (True ∨ ((p5 ∧ p2) → True))))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250953371599302147664409534324 : ((p1 → p4) ∨ (((((p1 ∧ p5) ∧ ((False ∧ p5) ∧ p4)) → p1) → p5) ∨ ((False → (((p4 ∧ p1) → (p4 ∨ (False ∨ p1))) ∨ p5)) ∨ p2))) := by
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
theorem thm_5_vars_114119975010219029151465313754 : (((True → ((((p2 ∧ (p4 → (False → True))) ∧ True) ∨ (p4 ∨ True)) → (((p5 → p1) → p1) ∧ p2))) ∨ (True ∨ (p5 ∨ p2))) ∨ (True ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807734220277789316853322057986 : (((p4 → ((p3 → (p1 ∨ p5)) ∨ ((p2 ∧ (p2 ∧ False)) ∨ (p2 ∨ (True ∨ ((((p1 → ((p3 ∨ p1) ∧ p3)) ∨ p5) ∨ False) ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306623649152648526561040474352 : (p1 ∨ ((p5 → p2) → (((((((p4 ∧ ((p5 ∧ p4) ∧ (p1 → (p4 ∨ False)))) ∧ p2) ∨ False) ∧ p5) ∧ (False ∨ (p5 ∨ True))) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37986703879137134029169709042 : (((((p3 ∧ (False ∧ (p2 ∧ (True → (p1 ∨ (p3 ∨ p2)))))) ∧ (((p2 ∨ ((False → p5) → p5)) → p5) ∧ p5)) ∨ (p2 ∨ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148238037440145544073928060911 : ((((p2 → (p2 → (((p1 → (p5 ∧ p4)) → p2) → False))) ∧ ((True ∨ p5) ∧ p3)) ∨ (False ∨ (p1 ∨ True))) ∨ ((p5 ∨ p2) → (p3 → False))) := by
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
theorem thm_5_vars_57440377612939445204799566533 : (((p4 ∨ (p3 ∧ p1)) ∨ (((False ∨ (False ∧ ((p4 → ((p3 → (p5 ∧ p4)) → p5)) → p4))) ∨ ((p2 → p4) ∨ p3)) ∧ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165738837942161073384076778167 : ((((True → (p5 → p1)) ∨ p5) ∨ (p2 ∨ (p2 ∧ (p4 ∧ (((True ∨ p3) ∨ False) → p4))))) ∨ (((True ∨ False) ∨ p1) → (True ∨ (p5 ∧ True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45128833691021072671649868149 : ((((p1 → False) → ((p1 ∨ (((p2 → (p5 → (p3 ∨ (True ∨ (((p4 → False) → p4) ∧ (p4 → False)))))) → p4) ∧ p3)) ∨ p1)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698928431364063945801951467826 : ((((p3 ∧ (False → (((p5 → ((p4 → p5) ∧ p5)) ∧ p2) → p2))) ∨ (((True ∧ (((p3 ∧ p3) → False) ∧ p2)) → (p1 → False)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51318622505950282444911678295 : (((p5 ∨ (((False → ((p2 → (False → (True → False))) → p3)) → p3) ∧ ((p1 → p2) → False))) ∨ ((p3 → True) ∨ ((p5 ∨ p5) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263385195624073602925086717560 : (True ∧ (((p3 ∨ ((((p2 → (p5 ∨ (True → p3))) ∨ (p5 ∧ (((False ∧ p3) → False) ∨ p5))) → p5) → p4)) → p5) ∨ (p1 → (p4 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



