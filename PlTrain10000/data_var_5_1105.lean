variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42290994373364256875046090681 : (((p2 ∧ (((p4 ∨ (p4 → (p3 ∨ False))) ∧ ((((((True ∧ p2) → p1) → (False ∧ p1)) ∧ p5) ∨ (False ∧ p2)) ∧ False)) ∧ False)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619773382875070545421246911664 : (((((p1 ∨ True) ∧ (p1 ∧ ((False ∧ ((p4 → p5) ∧ (p5 ∨ (p1 ∨ p4)))) ∧ (p5 ∧ ((p4 ∨ (False ∧ (p3 ∨ False))) → True))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157185909682739733478215709247 : ((((False ∨ ((p3 ∧ ((p5 → False) → ((p4 ∧ (p3 ∨ (p1 ∧ p4))) ∧ p2))) ∧ p4)) → p5) → p1) ∨ (p3 → ((False ∧ (p3 ∨ p3)) → False))) := by
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
theorem thm_5_vars_729732891272319144121849403326 : (((((p3 → False) ∨ p2) → (((p4 ∧ True) → (((p1 → (p5 → True)) ∨ ((p2 ∧ (((False ∧ False) ∧ False) ∨ p5)) ∧ p2)) ∨ p3)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111119276654488000167404788261 : ((((((p3 → False) ∨ ((p1 ∧ False) ∧ p3)) ∧ False) ∧ ((p2 → True) ∨ (((p3 → p2) ∧ ((p5 ∧ p4) → p1)) → True))) ∧ p5) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136366213684054714347412792109 : (((((p3 ∨ True) → p4) ∨ False) ∨ ((False → (False ∨ p5)) → ((p1 ∨ p2) → (p1 → (p3 ∧ ((False → p5) ∨ p1)))))) ∨ (False → (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138795172019655877479992566713 : ((((p2 ∨ True) → (p3 ∧ (((p4 ∨ p3) → (p3 ∧ (((p2 ∨ p4) → p3) ∧ p4))) ∧ ((p1 ∨ p3) → p1)))) ∧ True) → ((p4 → False) ∨ True)) := by
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
theorem thm_5_vars_780627797253149333513268534102 : (((p2 ∨ ((False ∨ ((False ∨ (p5 → (False ∧ (False ∨ p1)))) → p4)) → (((p1 ∧ ((((p1 ∨ p3) ∧ p1) ∨ p1) → p2)) ∨ p5) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596274434456651148685444305866 : (((((p3 ∨ (p4 ∨ (p2 ∧ ((False ∨ True) → False)))) ∧ (p5 ∧ ((p3 ∧ False) → ((p1 ∨ p1) → (p1 ∨ ((p1 ∧ p5) ∨ p4)))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174668759486975486541877421745 : (((False ∨ (p5 ∨ False)) ∧ (p2 → (p2 → (((p5 ∨ True) → p1) ∧ (False ∨ p3))))) → (((p3 ∨ (p5 ∧ True)) → (p4 ∨ (p5 → p2))) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325899497773360912147804459719 : (p5 ∨ (p4 ∨ (p1 ∨ (p1 ∨ (p1 → ((p2 ∨ ((((p2 → True) → (p5 ∨ True)) → p2) → p1)) ∨ ((p1 ∨ ((p5 ∨ p2) ∨ p1)) ∧ p1))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313321721258015805868209524995 : (p3 ∨ ((p3 ∨ ((((p4 ∨ False) ∧ p3) → (p1 → (p4 ∨ (((False ∨ p1) → p5) → p2)))) → ((True ∧ ((p5 → p3) ∧ p3)) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591666922164205240513699825986 : (((((((((p2 ∧ (((p3 ∨ (True ∧ ((p2 → p1) ∨ (p4 ∨ p4)))) ∨ p3) → p4)) ∧ False) ∧ p2) ∨ False) ∨ p3) ∨ (p3 → p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123321112294031142938355785883 : ((((p3 ∨ ((p2 → p1) ∧ (((p1 → p5) → (True → p4)) ∨ p2))) ∨ ((p5 ∧ False) ∨ True)) ∨ ((True ∧ (p4 ∧ p3)) ∨ False)) → (p5 → p5)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147764497446523209912341012345 : ((((p5 ∧ p5) ∧ (p3 ∧ (((p5 → (True ∨ p3)) ∨ (((p4 ∧ p5) → False) → p2)) ∧ (p3 ∨ p5)))) → False) ∨ (((False ∧ False) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80984950546992432431937263701 : (((((((p5 → p1) → (False ∨ p5)) → ((p5 ∧ (p5 ∨ p3)) ∧ p1)) ∨ (True → p4)) ∧ ((False ∨ p1) ∧ True)) ∧ ((p4 → p1) ∨ p3)) → p1) := by
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
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322419379955324169391936606137 : (p5 ∨ (((((False ∧ p1) → p1) ∧ ((p3 ∧ True) ∨ True)) ∧ (((p2 ∧ p3) ∨ False) ∨ (p4 → ((p4 ∨ (p2 ∨ p5)) ∧ (False → p1))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807398492103566555492702552661 : (((p4 → ((((p2 ∧ p5) → (p5 → ((p2 ∨ p2) ∧ p3))) → True) → ((p3 ∨ (((False ∧ p1) ∧ (False → p3)) ∧ False)) ∧ (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201197198287131005947103718246 : ((p1 → (False ∨ (p2 → ((p4 ∨ False) ∨ p1)))) → ((p1 ∨ p4) ∨ ((p1 → (p2 ∨ (p3 → (p5 ∨ p5)))) ∨ (((p1 ∨ True) ∧ False) → False)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314654592971824362311280401559 : (p3 ∨ (((True ∧ (((p2 → p5) → p2) → p1)) → ((p2 ∧ ((p3 ∧ p4) ∨ False)) ∨ p4)) ∨ (((p1 ∨ True) ∨ (p2 → p4)) ∨ (p2 → p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358336882310660699138227271688 : (p5 → (True → ((((((p3 ∧ ((p3 → ((False ∧ p1) ∨ p1)) ∨ True)) ∧ (p4 ∨ True)) ∧ p5) ∨ (p1 ∨ ((p3 ∧ p5) → True))) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65949693616678434541451449445 : ((p4 ∨ (p2 ∨ (True → (p4 ∧ (True ∧ ((((False ∨ p5) ∧ (((p4 ∧ (p5 ∨ p2)) ∧ (False → (p4 ∨ p3))) → p3)) → p2) ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607646463905191357198863240370 : (((((p4 ∧ ((p5 ∧ (p1 → ((p3 ∧ p1) ∧ p3))) ∨ (((p3 ∧ (p3 ∧ (p4 ∨ (p5 ∨ (True ∧ p4))))) ∨ p4) ∨ p2))) ∧ False) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_149100083261985886955983762738 : (((p4 ∨ (p1 ∨ False)) → (((((p3 ∧ (p2 → p2)) ∧ (False ∨ p2)) → p3) ∧ ((p2 ∨ p3) ∨ p5)) → p5)) ∨ (True ∨ (p2 ∨ (p5 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44867697894090977396151191132 : ((((p2 → (p5 ∧ p1)) ∨ (p3 → ((False → (p3 ∨ p2)) ∨ (((True ∨ (p4 ∧ (p4 ∨ ((p2 → p5) ∧ p4)))) ∨ p3) ∧ p1)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186635856627467470325315767225 : (((p3 ∨ (((True ∨ (p2 ∧ False)) ∨ p1) → False)) → (p1 ∨ p5)) → (((p2 → (p1 → (p4 → (p4 → (p5 → (p3 ∧ p2)))))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117183828401485464000920716300 : ((True ∧ (((((p5 ∧ ((p2 ∧ (p4 ∨ p4)) ∨ p1)) → True) → (p4 ∧ (p2 → p5))) ∨ ((p3 → p2) ∧ p4)) → (p1 ∨ False))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709413987856597488865661948218 : ((((p1 ∧ (((p3 ∨ p5) → p5) → (False ∨ False))) → ((((((p4 ∧ p1) → p3) → p4) → ((p3 ∧ (True ∧ p1)) ∧ False)) ∨ True) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244938791898429657112899425682 : ((p1 ∧ p3) ∨ ((p2 ∨ (((False ∨ (True ∨ p3)) ∧ False) ∨ (((p4 → p4) ∧ True) ∧ True))) ∨ (((p5 ∧ (p5 → (p1 ∧ True))) ∧ p4) → False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47073966185399680554786269833 : ((((p3 → (((False ∧ p5) ∨ (p2 → (p1 ∨ (((p4 → p2) ∧ (p2 → p3)) ∨ (p3 ∧ True))))) ∧ p1)) ∨ (p5 → False)) ∨ (p5 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798376838058514215242040692442 : (((p1 → ((p5 ∧ (((True → p4) → ((p3 → p1) → True)) ∧ (False ∨ p2))) ∧ ((p1 → (False → p5)) → ((p3 → p2) ∧ (p2 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135949487651211767630043925705 : (((((True ∧ p5) ∨ (p5 ∧ p4)) ∨ ((False → p3) ∧ p3)) ∧ ((p3 → True) → ((True ∨ ((p5 ∨ False) → p1)) ∧ p4))) ∨ (True ∨ (p2 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245923645426147558786373115603 : ((p3 ∧ p5) ∨ ((p5 ∨ p3) ∨ (((False ∨ p1) ∧ ((p2 → p4) → False)) ∨ (((((p4 → p5) → p5) ∧ (p4 ∨ (p2 ∧ p2))) ∧ p4) ∨ True)))) := by
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
theorem thm_5_vars_179602574207064782644489611180 : ((p3 → ((p5 ∨ False) ∧ (((p3 ∧ True) → (True ∧ p1)) ∧ (False ∨ p4)))) ∨ ((((True → (p5 ∧ True)) ∨ True) ∧ ((p5 → True) ∨ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_157576729169621616118832609421 : ((((p4 → p4) ∧ ((p3 → (p2 → ((p3 → False) ∨ True))) ∨ (p3 ∨ (True → p4)))) → (p3 ∨ p5)) ∨ ((p3 → p3) ∧ ((p1 ∨ True) ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157929115915433271815802507824 : ((((p3 ∧ (p3 → ((False ∧ p2) ∨ p2))) ∨ p4) ∧ (((p2 ∧ p1) → (p5 ∧ p5)) ∧ (p4 → False))) ∨ ((True ∨ (p1 ∧ p2)) ∨ (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324863413406106062746744147503 : (p5 ∨ ((p2 → p2) ∧ (p3 ∨ (((((False ∧ (True ∨ p1)) ∨ p2) ∧ (((True → p3) → p5) → (p5 ∧ p4))) → p5) ∨ ((False ∨ False) → p1))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39620286546017156172073335567 : (((p2 ∨ (p5 ∧ (((((((p3 ∧ (p1 ∨ True)) ∧ (p4 ∧ True)) ∨ p4) ∧ p2) ∨ ((False ∨ p2) → (True ∨ p3))) ∧ p1) → p3))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157653579796337203293806930572 : (((((((p4 → ((False ∨ False) ∨ p1)) → (p4 → p2)) ∨ p5) → False) ∨ p4) ∨ (p3 ∨ (False ∨ p2))) ∨ ((((p1 ∧ False) → p1) → False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ False) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806228148745105833809523355972 : (((p4 → (((p1 ∧ ((p4 ∨ p3) → (False ∨ ((p3 → (((p2 → p5) ∨ True) → ((p4 ∨ True) ∧ p4))) → p3)))) ∨ (p2 → p5)) ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864732435375482583481060740251 : ((((((True → False) ∧ ((p1 → (False → p5)) ∨ p3)) → (((((((p1 → p5) → (p2 → p3)) → p1) → True) → p1) → p3) ∧ p2)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → False) ∧ ((p1 → (False → p5)) ∨ p3)) → (((((((p1 → p5) → (p2 → p3)) → p1) → True) → p1) → p3) ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h15 := h11 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h18 := h11 h17
      -- False on the left can always be used.
      apply False.elim h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62837292303737409312711358838 : ((p4 ∧ ((((p2 ∧ p1) → (p5 ∧ True)) ∨ False) ∧ (p2 ∨ (((p5 ∨ p5) ∧ False) ∨ (((p1 ∨ p3) ∨ (p1 ∨ p3)) → (False ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50779673293332926481448589977 : (((p3 ∨ (((p1 ∨ p2) ∧ ((p5 ∧ (((p5 → p4) ∨ (p3 ∨ p3)) ∧ p2)) ∨ p2)) ∧ (p3 ∧ True))) → ((p1 → (False ∨ p1)) ∨ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h6.left
          let h17 := h6.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h18
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h6.left
            let h22 := h6.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h23
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h6.left
            let h26 := h6.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h27
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h6.left
        let h30 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h31
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h6.left
          let h40 := h6.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h41
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- Conjunctions on the left can always be decomposed.
            let h44 := h6.left
            let h45 := h6.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h46
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h46
          case inr h47 =>
            -- Conjunctions on the left can always be decomposed.
            let h48 := h6.left
            let h49 := h6.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h50
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h50
      case inr h51 =>
        -- Conjunctions on the left can always be decomposed.
        let h52 := h6.left
        let h53 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h54
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326181003652186769657256950159 : (p5 ∨ (p2 → (((p2 ∨ (((p3 → False) ∨ ((p2 ∧ p5) ∨ p1)) → p1)) → p3) ∨ (((p1 ∨ ((True ∨ False) → p5)) ∨ (True → p4)) → True)))) := by
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
theorem thm_5_vars_623943146723664517163722909265 : ((((p2 ∨ (((((False ∨ (p4 ∧ p1)) ∨ ((p2 ∧ (p1 → (False ∧ (p5 ∧ (p1 ∨ False))))) ∨ (p4 ∧ False))) ∨ p2) ∨ p5) ∨ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207910573026283176735835375728 : (((p3 ∧ (p4 → True)) ∧ (False ∨ p1)) → ((((p4 → p1) ∧ (p5 ∧ ((p4 ∧ ((p4 → (p1 ∨ False)) → p4)) ∧ True))) ∧ True) ∨ (p1 ∨ p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301358966066167671800377487592 : (False ∨ ((((p4 ∧ p3) ∨ p2) ∧ p2) ∨ (p5 ∨ ((p2 → ((p1 → ((False → p2) ∧ p1)) ∧ ((p5 ∧ (p4 ∧ (p5 ∨ p2))) → True))) ∨ False)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622457806232895415846761647887 : ((((p3 ∧ ((False → False) → ((p2 ∨ ((p3 ∨ (p2 → ((True ∧ (p5 ∧ p2)) → (p4 → (p3 ∨ p3))))) ∨ (p2 → p3))) ∨ p1))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113055790085393630801751938359 : (((p2 ∨ ((((False ∨ p2) ∨ (p3 ∨ (True ∧ ((True ∧ (p1 → (p2 ∧ p5))) → (True ∨ False))))) ∨ (p3 → True)) ∨ p1)) → False) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357021463319658425858259562180 : (p5 → (((p2 ∨ p4) → False) ∨ ((p2 ∧ ((False → ((((p4 ∨ False) → p5) ∨ (((False ∧ False) ∧ p3) → True)) → p5)) ∧ (p2 ∧ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671291362274668605925328843081 : ((((p5 ∨ ((p4 ∨ ((p2 → p5) ∧ p1)) → ((p1 ∨ (((p2 ∧ p1) ∧ p5) ∧ p3)) ∨ (p1 → (p1 ∧ p5))))) ∨ (True ∧ (True ∨ p2))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681452569184418769479714027321 : ((((p4 ∨ ((p4 ∨ (((p3 ∧ (p2 ∧ p4)) ∨ (True → (p4 → p2))) → (p5 ∨ p2))) ∧ (True ∧ p1))) → (p3 ∨ ((p1 → p2) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321290892190753083791328625853 : (p4 ∨ (p5 ∨ ((p4 → ((p1 → ((((True ∨ (p2 ∧ ((p3 ∧ p5) ∨ False))) ∧ p2) ∧ p3) ∧ ((p2 → p3) ∨ (False → p1)))) ∨ p4)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167737163444029666417431059354 : ((((((p2 ∨ False) ∧ p5) ∧ p2) ∨ ((p1 ∧ p1) → (p4 ∨ p3))) ∨ (p4 ∨ (p5 → False))) → ((((True → True) ∨ p5) → p4) → (p2 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h11 : ((True → True) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h12 := h2 h11
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((True → True) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : ((True → True) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h21
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790967636448650803557674207970 : (((p5 ∨ (p5 → ((((False ∨ p3) ∨ True) ∧ p5) → (((((True ∧ p1) ∨ (p2 ∧ p3)) ∨ True) → (False ∨ (p2 ∨ p5))) ∨ (p4 ∧ True))))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h18
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42524715888903458344534480031 : (((False ∨ (p5 → (((((p1 ∨ p2) ∨ True) → (((p5 ∨ True) → (p2 ∧ p5)) ∨ ((p4 ∧ True) → p2))) → p3) ∧ (p4 → p2)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722271005584535388547361764948 : (((((False ∧ True) ∧ p1) ∧ (((p5 → (p3 → ((((p4 → p3) ∨ p3) → ((True ∧ p4) ∨ p1)) → p4))) → p1) ∨ ((p4 ∧ p5) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793567808332105972121154669674 : (((True → (p3 ∨ (((((p2 ∧ ((p4 → (p3 ∧ p5)) ∨ (False → True))) ∧ p4) ∧ p1) → ((p5 ∧ p5) ∨ ((p4 → p5) ∨ p5))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337356687674777159499315462310 : (p1 → ((((p1 ∧ ((((p5 ∧ p3) → p3) ∨ p1) ∧ (((p5 → p5) → (p4 ∨ p4)) → False))) ∧ False) ∨ (p2 ∨ True)) ∨ ((p3 ∧ p3) ∧ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241823472943001517000612022660 : ((p1 → p1) ∧ ((p2 ∨ ((p5 → (((p2 ∧ (p1 ∨ (((True ∨ (p2 ∨ True)) → True) → True))) ∨ p1) ∨ p2)) ∨ ((p4 ∧ p4) ∨ True))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_336488657846488666562222679136 : (p1 → ((p5 → ((p2 ∨ p5) ∧ ((p1 ∨ (((((p3 ∨ p3) ∨ True) ∨ True) ∨ True) ∧ p3)) → (((p2 → False) ∧ p1) ∨ (p3 ∨ False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166309554751616335251833600744 : ((p5 ∧ (((p2 → (p1 ∧ ((p2 ∧ (p5 ∨ (p3 ∨ p5))) → p3))) ∨ (True ∧ p4)) ∧ p3)) ∨ ((p2 → p4) → ((p5 ∧ False) → (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698070477407476304089943449549 : ((((((p1 ∧ p5) ∨ (p3 ∨ (p1 → ((p5 ∧ p1) ∧ p5)))) ∨ p1) ∨ ((p1 → ((p2 ∨ (p2 ∨ (p1 → True))) ∧ p2)) ∨ (p5 ∨ True))) ∨ p4) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136117759788522443540942570766 : (((p3 ∧ (p4 ∧ ((p4 ∨ (p2 ∧ p5)) ∨ p4))) ∨ (p2 ∧ ((p1 ∧ (p3 ∧ (p2 ∨ ((p5 → p2) → False)))) → True))) ∨ (p1 → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65736909169007355481935686583 : ((p4 ∨ ((True ∧ (((((False → p5) ∨ p2) ∨ ((True → p5) ∨ (False ∨ p4))) → (p5 ∨ p5)) ∨ (p5 ∧ p2))) ∧ (p5 → (p3 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335858074105795827145706684113 : (p1 → (((False ∧ (p4 → ((((True → p4) → True) → p5) ∨ False))) ∨ ((p3 ∧ ((p4 ∨ ((p5 → p3) → p1)) → (p3 ∨ True))) ∨ p1)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336368383100747469637913464258 : (p1 → (((p5 ∨ True) → (p5 ∨ ((p4 ∨ ((p2 ∧ p4) ∨ ((p2 → (p4 ∨ p1)) → (p3 ∨ ((p2 → (p4 → p4)) ∧ p1))))) ∨ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355667262340253195426557823140 : (p5 → (((((((False ∨ ((p2 → p1) ∨ False)) ∨ (((p4 ∧ p5) → ((p4 → p1) ∨ True)) → p1)) ∨ True) ∨ p5) ∨ False) → False) → (p1 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((False ∨ ((p2 → p1) ∨ False)) ∨ (((p4 ∧ p5) → ((p4 → p1) ∨ True)) → p1)) ∨ True) ∨ p5) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((((False ∨ ((p2 → p1) ∨ False)) ∨ (((p4 ∧ p5) → ((p4 → p1) ∨ True)) → p1)) ∨ True) ∨ p5) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352287962166185641548110486991 : (p4 → ((p1 ∧ ((False → p5) ∨ p1)) → ((p2 → ((p5 ∧ p3) ∨ (False ∧ (p2 ∨ (True ∨ (p1 → p2)))))) ∨ (p4 ∨ (p5 ∧ (p5 ∧ p4)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314928323910253879353769146061 : (p3 ∨ (((p1 ∨ p4) ∧ (((p4 ∧ (True ∧ p2)) → p4) → p1)) ∨ ((p5 → (p3 ∧ (p1 ∨ True))) ∨ (p4 → (False → (False → (p5 ∨ p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244370832611429612582458984040 : ((False ∧ p1) ∨ (((p1 → (((((True → True) → False) → p1) ∨ (((True ∨ (p4 → (False ∨ p1))) ∧ p3) ∨ (False ∧ False))) → p4)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673232271880841585520861418683 : (((((True → (p1 ∧ (False → (p1 ∧ ((True → p1) → False))))) → ((p3 → (p3 → ((True ∨ p4) → p4))) ∧ p5)) → ((p4 ∧ p1) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136705137654216158805885277264 : (((p1 ∧ p3) ∧ (p4 ∧ ((p5 → (p3 ∧ True)) ∧ (p3 ∧ (((p3 ∧ ((p3 → p1) ∨ p4)) → (p1 → p1)) → p1))))) ∨ ((True ∧ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660257430810746657488159039613 : ((((((False → p3) ∨ (p4 → (((((False ∧ (True ∧ p4)) ∧ (p5 ∨ p1)) ∨ False) ∧ (p5 → p3)) ∧ (p2 ∧ p2)))) ∨ p3) → (p2 ∨ True)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148100329752839280856882628107 : (((((True → p1) ∨ (p5 ∨ (((p2 ∧ False) ∨ ((p5 ∨ True) ∨ p1)) → p1))) ∨ (False ∧ p2)) → (p3 ∨ False)) ∨ (p1 ∨ ((False → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54530476028562980221486079999 : ((((p5 ∨ p5) ∨ (p5 ∧ ((p3 ∧ p2) → p4))) ∨ (((True ∧ p3) ∧ (p3 ∧ (p2 ∨ (True → False)))) ∧ (False ∧ (p4 ∨ (False ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346873056730760547565106541704 : (p3 → (((((True ∧ p5) ∨ p2) ∧ (p1 ∨ (p1 ∧ p3))) → (((p4 → False) ∧ (p2 → p5)) ∨ p3)) ∧ (((True ∧ (p2 ∧ False)) ∧ p2) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Implications on the right can always be decomposed.
  intro h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164772738203155019473875732363 : ((((p4 ∧ (p2 ∨ (True ∧ ((p1 ∧ p3) ∨ p1)))) ∨ (False → (False ∧ (p3 ∧ p2)))) ∨ p1) ∨ (((True ∧ p2) ∨ ((p5 ∨ p2) ∨ p1)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205295802168060384589116236534 : (((p4 ∧ (False ∨ p4)) ∨ (p4 ∨ False)) ∨ (((p1 ∨ p1) ∧ ((p1 ∨ p5) ∨ (p4 ∧ ((p5 ∧ False) ∧ (p2 ∨ (p4 → p4)))))) → (p1 ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67766375869574354303597660559 : ((p2 → ((((((p2 ∧ p3) → False) ∨ (p4 ∨ True)) ∨ p2) ∧ (((p3 ∧ ((p1 ∨ (p3 ∨ p1)) ∨ p1)) ∧ (p4 → p2)) ∨ p5)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48180457597878992509001303481 : ((((p1 ∧ p2) ∨ (((p5 ∧ p5) ∧ ((p1 ∨ p1) → ((True ∨ (p3 ∨ False)) ∨ ((True ∧ p1) ∧ (p1 ∧ p2))))) ∧ True)) → (p2 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41969090486250943548691310313 : ((((False ∨ True) ∧ ((p1 ∨ (p3 ∨ p3)) ∧ (((((True → p5) → p4) ∧ True) ∨ p5) → (True → ((p5 ∧ p4) → (p5 → p2)))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56529839684032499681114255947 : (((True ∨ (p1 → (True ∨ p5))) → (((p5 ∧ p4) ∨ p2) ∨ ((p4 → ((p5 ∨ (True → ((False → p2) ∧ (p4 ∧ p3)))) → p1)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26195512311232913415987048381 : (((True → True) ∧ (p5 → (((p1 ∧ (p2 → p2)) ∨ ((False → p3) → (p1 → p5))) ∧ (p1 ∨ (((p1 ∧ p1) ∨ (p4 ∨ True)) ∨ p4))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313107636507522583738599834477 : (p3 ∨ ((((((((p5 ∨ p1) → (((True → p5) ∧ ((p2 ∧ p1) → False)) ∧ False)) → p5) ∧ p4) ∧ p2) ∧ False) ∨ ((p3 → p1) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82447615225917183151614688954 : (((p1 ∧ ((p5 ∨ (p4 → (((p2 ∨ False) → False) → p1))) ∧ ((p1 ∨ ((False ∧ True) ∧ True)) → False))) ∧ ((p4 ∨ False) → (True → p1))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ ((False ∧ True) ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : (p1 ∨ ((False ∧ True) ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135663527694375241365734957151 : (((p1 ∧ (((p1 → p5) ∨ ((((p1 → p4) ∨ p5) → p5) ∧ p5)) ∨ (p3 ∧ p2))) → ((p2 → (False ∨ p3)) ∨ p5)) ∨ ((p4 ∨ True) ∧ p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243420297721424301364103586655 : ((p5 → True) ∧ (((p2 → (p4 ∨ ((p1 → False) → ((p3 → (p3 ∧ True)) → p5)))) → p4) ∨ (((p4 ∧ p1) ∧ (p4 → True)) → (p1 ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45897468735189478367509877594 : (((p4 → ((True ∨ ((True → ((True ∧ (p2 ∨ p1)) ∧ (p4 ∨ False))) → (p5 ∧ ((p5 ∨ (p3 ∧ True)) ∧ (False ∧ True))))) ∧ p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256778033925509502833521954316 : ((p1 ∨ p2) → ((p3 → (((((p1 → p5) ∧ (True ∧ (p1 ∨ True))) → p3) → ((p4 ∧ p2) ∨ p5)) → p2)) ∨ (((True ∧ p4) → True) → p1))) := by
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
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641054873576716617862252510710 : (((((p4 ∧ p3) ∨ (((p2 → (p5 → p2)) ∨ True) ∨ (p5 → (True ∨ (p1 ∧ ((p2 ∧ ((p4 ∨ p1) ∧ (True ∧ p1))) ∨ p3)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306068387302713177548898261886 : (p1 ∨ ((True → (False ∧ (p4 ∨ p5))) → ((p2 → ((False → p2) → ((True ∨ ((p1 ∧ True) → ((p5 ∨ p3) → p2))) → (True → p5)))) ∨ p3))) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339864917359196159540426354324 : (p1 → (True → ((False ∨ (((p5 ∧ ((p4 ∧ (True ∨ p4)) ∨ p1)) ∨ (True → p1)) ∨ (p3 ∨ p2))) ∧ (True ∧ (p2 → (p4 ∨ (p5 ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217452972709819220745300802329 : (((p4 → (p3 → p4)) ∨ p3) → (p1 ∨ ((p5 ∨ ((((p3 ∧ p2) ∨ (p5 → ((True ∨ p3) ∨ False))) ∨ (p5 ∨ (True ∨ True))) ∨ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
theorem thm_5_vars_156800400195805294031110539678 : (((p5 ∧ (((p4 ∨ (((p3 → True) ∧ p4) ∨ (p2 ∨ p2))) ∨ p4) ∧ (p3 ∨ (p3 ∨ p1)))) ∧ p5) ∨ ((p4 → (True ∨ False)) ∨ (p4 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172613223311665082213705289033 : (((p3 → (p4 ∨ False)) → (False ∧ (True → (p2 ∧ ((p1 ∧ p2) → (p1 ∧ p3)))))) ∨ ((p4 → (((p5 → False) ∧ p4) ∨ (p4 ∧ p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68993670020919602737147165832 : ((p5 → (((((((p1 ∨ p1) → p5) → (p1 → False)) ∧ p1) ∧ ((p3 ∨ (p1 ∨ ((True ∨ p4) ∨ p3))) ∨ p3)) ∧ (p2 ∨ p2)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326123237384540187538164121094 : (p5 ∨ (p1 → (((p2 ∧ (p1 → ((True ∨ False) → p4))) ∧ p4) → ((p1 → (p3 ∧ (p5 ∧ p4))) ∨ ((p1 ∧ (p3 → p2)) ∧ (False ∨ p1)))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149109688089303764779363395264 : (((p4 → (p3 → p4)) → (((((p1 → p3) ∨ (p3 ∧ (p1 ∨ p1))) ∨ True) ∨ p3) ∨ ((p3 → p4) → p4))) ∨ (p2 → ((p2 → p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157459506660463043664395399142 : ((((p5 → ((p3 ∨ p1) → ((p5 ∧ ((p5 ∧ p2) → p4)) ∧ (p3 ∧ False)))) ∧ True) ∨ (p2 ∧ p3)) ∨ ((True → (p5 ∧ (p1 → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



