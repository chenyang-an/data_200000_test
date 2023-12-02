variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340736322015229548230181072514 : (p2 → ((((((((True ∧ (((p2 ∧ True) → ((p3 ∨ p3) → False)) ∧ p1)) ∨ p5) → p5) → (p5 ∧ p5)) ∧ (p1 → p3)) → p4) ∨ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302759674537458632092033977803 : (False ∨ (p4 ∨ ((p4 → ((p3 ∧ ((((p4 → p1) ∨ p1) ∧ (False ∧ p4)) ∨ p4)) ∧ (p3 ∧ p1))) ∨ (p1 → ((p5 → p1) → (p3 ∨ p1)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190802372067652682951531091338 : ((((False ∨ p3) ∧ ((p5 ∧ p4) → True)) ∨ (p2 ∨ False)) ∨ (p1 → (((p4 ∧ (False ∧ True)) → True) ∧ ((False ∨ ((False → True) ∨ p3)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638057345901327567948199342141 : ((((((p5 ∧ p3) → ((p3 ∧ p3) ∨ (p1 → p5))) ∨ ((((p5 ∧ p1) ∧ (True ∨ p3)) ∧ (p3 ∨ p1)) ∧ (p1 → (p5 ∧ False)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191145208598718811726337679844 : ((((p4 ∨ p1) ∨ p2) ∨ ((p2 ∨ p1) ∨ (p1 ∨ p1))) ∨ ((False → (p2 → (p2 → (p2 → ((((p5 ∨ p3) → True) ∨ False) ∧ p5))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227836186450695006275970112430 : ((p2 ∧ (p4 ∧ p3)) ∨ ((p5 → (False ∧ (p1 → (((p3 ∨ (p3 ∨ (p4 ∨ p5))) → (((p1 ∧ p5) ∧ True) ∧ (p2 → False))) ∧ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66366686772958530910626062360 : ((p5 ∨ (p1 ∨ ((((p3 ∨ ((p2 ∧ p4) → p3)) → ((p4 ∧ p3) ∨ False)) → p2) ∨ ((p2 → (p3 → ((False ∨ False) ∨ p2))) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147706855119883124491670326026 : (((((((p4 ∨ p4) ∧ (p3 → p4)) ∨ (p1 ∨ p4)) ∧ True) ∨ (p1 ∨ ((p1 ∧ True) ∨ (p3 → p4)))) → False) ∨ (False → ((False ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647476465046448206362129412035 : ((((p4 → (True → ((p3 → ((p5 ∨ (p1 ∨ p2)) ∨ (p2 ∨ True))) → ((True ∨ (True ∧ (True → True))) ∨ ((p2 ∧ True) → p5))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165417146961496758734590060970 : ((((((False ∨ p4) ∧ True) ∨ (p3 ∨ (p4 → False))) ∨ (p4 ∨ True)) → ((False ∨ False) ∧ True)) ∨ ((p1 ∨ (p4 ∧ False)) → (p1 ∧ (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59175785147374026679833494860 : (((False ∨ p5) ∨ (((p2 → p1) ∨ (p1 ∨ (((p3 ∨ (p4 ∧ (p5 ∧ ((p2 → (p2 ∧ p3)) ∨ (p2 ∨ p4))))) ∨ p4) → False))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64583887992837184667701392057 : ((p1 ∨ ((True ∨ p2) ∧ (p3 → ((p4 ∨ (False ∨ (p4 ∨ ((p2 ∧ ((p1 ∧ p2) → (p5 ∧ (p2 ∧ p2)))) ∨ (p5 ∨ p3))))) ∧ True)))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702446636306965977763711884138 : (((((p5 ∧ (p1 ∨ ((p4 ∧ (p2 ∨ p5)) ∨ True))) ∨ p2) ∨ (((p1 ∧ p2) → (((p1 ∧ False) → (False → p3)) ∨ (p4 ∨ p1))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157486497790721325625260690419 : (((((p2 ∨ (p3 ∧ ((p4 → p1) ∨ True))) ∨ p5) ∨ ((p2 ∨ (True ∧ p5)) → p4)) ∨ (p2 → True)) ∨ ((p2 ∨ (p1 → (p4 ∨ p3))) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227830540632485066554012792855 : ((p2 ∧ (p3 ∧ p3)) ∨ (((p1 ∧ p2) → (p4 ∨ (((False ∧ False) → (True ∨ False)) ∧ ((p4 ∨ ((p2 → False) ∨ p5)) ∨ (False → True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238049570237645781296993213077 : ((True ∨ p2) ∧ (((((p5 → (p5 → ((False → ((p4 ∨ p2) ∨ False)) → p3))) → p5) → (((False ∨ p5) → p2) ∨ p4)) ∨ (p1 ∨ True)) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_355630336332834329941623364837 : (p5 → ((p4 ∨ ((p2 → (False → (((False ∨ False) ∨ (((p3 → p3) ∧ ((p5 ∧ p2) ∧ p5)) ∨ (True ∨ p4))) ∨ p3))) → p3)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675655401303583034383520145654 : ((((((p2 ∧ ((p5 ∨ ((p5 → (p1 → False)) ∨ (p2 ∧ p2))) ∨ p5)) ∧ (p2 ∨ p4)) → (True → p1)) ∧ (p3 ∧ ((p4 ∨ p3) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625646751682143254944490986684 : ((((p1 → (((((p3 ∨ True) ∧ (p4 ∨ p3)) ∨ (((False ∨ p5) → (p5 → (p1 → p5))) ∧ (False → False))) → False) ∧ (p1 → p3))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_113459351267629880068401529702 : (((((p3 ∧ ((p3 ∨ (((True ∨ ((False → p5) → True)) ∨ p4) ∨ p2)) → p4)) ∨ (p4 ∨ (p4 ∧ p3))) → False) ∨ (p2 → True)) ∨ (p5 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190244344362020417304385260900 : ((((((p5 ∧ False) ∧ p3) → (p4 → False)) ∧ False) ∨ p4) ∨ ((p5 ∨ (((True → (p3 ∨ p2)) ∧ (p2 ∨ (p5 ∧ p5))) ∨ (p5 → p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_110882772376010122424101265877 : (((((((p4 ∧ (((((True ∨ p2) ∧ p5) ∨ p5) ∧ p2) ∨ True)) ∨ p3) ∨ p5) ∨ ((p2 → (p2 ∨ p5)) ∨ p3)) → p3) ∧ p5) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126462558213422794671618785790 : ((p2 ∧ ((((p1 ∨ ((True ∧ (p3 ∧ p5)) ∧ p1)) ∧ p3) ∨ (True → (True ∧ ((p2 ∧ p3) ∧ (False ∧ p1))))) ∨ (True ∨ p4))) → (False ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136347161188985097567625097530 : (((p4 ∨ ((p1 → True) → False)) ∧ ((p5 ∧ p4) ∨ (((True ∨ ((p3 ∨ p2) ∨ False)) → True) → ((p5 ∧ p1) ∨ p5)))) ∨ (p1 ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38766944703763039646431897082 : ((((True → (p5 → (False ∧ False))) ∧ (p2 ∨ ((p4 → ((p2 ∨ (p4 ∨ (((False ∧ False) ∧ (p4 ∧ p2)) ∧ p5))) ∧ p1)) ∧ p3))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51332896800886874081190111002 : (((p2 → ((p3 ∧ (((p4 ∨ p2) → p1) → ((p5 → True) → (p5 ∧ p3)))) ∨ (p1 ∧ p5))) ∨ (p5 → (((p4 ∧ p4) ∧ p4) → p4))) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178404516740639418026418828699 : ((((p2 ∨ False) ∨ (((p1 ∧ p1) ∧ (p1 ∨ p5)) → p3)) → (False ∧ True)) ∨ (p2 → (((((False ∧ p1) → True) ∨ p2) ∧ (False ∨ False)) → p1))) := by
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
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61092003356514353543483886989 : ((False ∧ ((((False ∧ (((True ∧ p4) ∧ (False ∧ p1)) ∨ (p4 ∨ p1))) ∧ (p3 ∧ p3)) ∧ True) ∨ (p3 ∨ ((p1 ∧ (p2 ∧ p3)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304860620269736448110436854144 : (p1 ∨ (((p2 ∨ ((p5 → p3) ∧ p5)) → ((p5 ∨ (((p3 ∧ True) ∨ (((p3 ∨ (p3 ∨ p4)) → False) ∧ p1)) ∨ True)) ∧ False)) → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ ((p5 → p3) ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788277008852070770950569154755 : (((p5 ∨ ((p4 → ((p2 ∧ ((((p5 ∧ p4) → (p3 → p4)) → False) → (p5 ∨ (True ∧ ((p3 → (p2 → p3)) ∧ p3))))) ∨ False)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43431929884286897900666133953 : (((((((p1 → p5) ∧ p3) → p2) ∨ (True ∧ (p1 ∧ (((p1 ∧ p1) ∧ (p4 → (((p2 ∨ p3) ∨ p2) ∧ False))) ∧ p5)))) ∨ p1) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59377731956252753635260376656 : (((p5 ∨ p5) ∨ (p4 → ((((p4 ∨ p4) ∧ p1) → (True → (p1 ∧ ((p4 → (((p5 → p3) → p5) ∧ True)) ∧ p5)))) ∨ (True → p4)))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179222327409064598687459124358 : ((p4 ∧ ((True → p1) ∧ (((((True ∧ p4) → True) → False) → p1) → p3))) ∨ (p4 → (p5 → (False → ((p4 → (p4 → (p2 ∧ True))) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677373140954112919914077721850 : (((((((p2 → (p3 ∨ (p3 ∧ (False ∧ False)))) ∨ (p4 ∨ (True → ((p4 ∧ p1) ∧ p4)))) ∧ True) ∨ p2) ∨ (p5 → (p5 ∨ (True ∧ False)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789322154165162770782158530505 : (((p5 ∨ ((((p5 ∧ (p3 ∨ p1)) ∨ ((p2 → ((p5 ∧ (True ∨ False)) → p1)) ∧ p4)) → p5) ∨ (p5 ∧ (((p3 → p2) → True) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304977649720888130004658305526 : (p1 ∨ ((((p3 → (((p1 ∧ (p1 ∨ p4)) ∨ p3) ∨ (p2 → False))) ∧ (p1 ∨ ((False → False) ∨ (True ∧ p5)))) ∧ p4) ∨ (True ∧ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_225850172624813479047273902656 : (((False ∧ p1) ∨ p1) ∨ (p3 ∨ ((p3 ∨ True) ∨ ((p1 ∧ ((p5 ∧ (((False ∨ (True → True)) → False) ∧ (False ∧ p5))) ∧ (p4 ∨ p3))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942197288744632575994452533301 : (((((p4 → (p2 ∧ p1)) ∧ p5) ∧ ((True ∧ p2) ∧ (((False → p1) → (p4 ∧ p4)) ∧ (p3 → ((p1 ∧ ((p4 → False) ∨ True)) ∨ p5))))) → p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_13630889195337035276253486202 : (((((((True ∨ p4) ∨ True) → (p5 ∧ (((p3 ∨ p5) ∨ True) ∧ (p4 ∨ (p4 ∧ (p2 → (p1 ∧ p1))))))) → p4) ∧ True) ∧ (p4 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136548589662415617525301657677 : ((((p1 → p1) ∧ False) ∨ ((p3 → (((p3 ∨ True) ∧ p1) ∨ p4)) ∨ (p4 ∧ (p5 → ((True → (False → p1)) → p3))))) ∨ ((p5 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245004637741828263073118049331 : ((p1 ∧ p4) ∨ (((((p4 ∨ True) → p1) → p2) → p1) ∨ ((True ∧ (((((False ∨ p5) ∧ p5) → False) ∨ p4) ∨ p3)) → (True ∨ (False → p2))))) := by
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
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307427170534051895448435992664 : (p1 ∨ (p5 ∨ ((p1 → (((p3 ∨ ((p1 → ((p1 ∧ p3) ∨ False)) → p5)) ∧ p5) ∧ ((True ∧ ((p3 → (True ∨ False)) ∨ p3)) → p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111820582385731531583684639252 : (((((((p2 → p5) ∨ (((p5 → p1) ∧ False) ∨ (((False → False) ∨ True) ∨ p3))) ∧ False) ∨ False) ∧ (p5 ∨ (p4 ∧ p5))) ∨ True) ∨ (p1 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113262849478446032371033332375 : ((((p3 ∨ (((False → True) → (True ∧ (p1 ∧ (((p1 ∧ p1) ∧ False) → False)))) ∨ p1)) ∧ (p5 → (p3 → p1))) ∧ (False ∨ p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247783183089153785796242142544 : ((p1 ∨ p1) ∨ ((((((((True → (p5 ∨ True)) ∨ (p3 ∨ (p3 ∨ p3))) ∧ p5) → p1) → p2) → (p2 ∨ (p2 ∧ p1))) ∨ True) ∨ (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671541068155300085368423252147 : ((((p4 → ((p4 ∧ ((p3 ∨ ((p2 ∧ (p3 → False)) → (p3 → p2))) → (p5 ∨ (p2 ∨ p3)))) ∧ (p3 ∧ False))) ∨ ((p5 ∨ p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114848424551656827383753729533 : ((((p2 ∧ ((p3 → (((p5 → True) → (p3 → p2)) → p2)) ∨ p5)) ∨ p1) ∨ (p5 → (((p1 ∧ (p1 ∧ p4)) → True) → False))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57760207218296180784389818357 : ((((p3 → p3) → p4) → (((((((p5 → (p2 ∧ False)) → (((p2 ∨ False) ∧ p1) ∧ p3)) ∨ p4) → p2) ∧ (True → True)) → p2) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65131126339017759876479279428 : ((p2 ∨ (p1 → ((((p4 ∨ p3) ∨ (p2 ∧ False)) ∧ p5) ∨ ((p2 ∨ (p3 ∧ p3)) → ((((True → p4) ∨ (True → p1)) ∨ p1) ∧ True))))) ∨ p2) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58750619832457632189841409981 : (((p4 → True) ∧ ((p3 ∨ (((p2 → (p3 ∨ (p2 ∧ (p3 ∨ p1)))) ∨ (p5 ∧ True)) → False)) ∨ ((p2 → (p2 → (p4 ∨ p5))) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66201976590632295503818856037 : ((p5 ∨ (((False ∨ (False → ((p2 → True) ∨ p4))) → (((True → p1) ∧ p4) ∧ p5)) ∧ (p3 → ((p5 ∧ (True ∨ True)) ∧ (p2 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177920588394290836299972564059 : ((((p3 ∨ ((p2 ∧ (p1 ∨ True)) ∨ p3)) ∨ ((True ∧ True) ∧ p5)) ∨ p3) ∨ ((p5 → True) ∧ (True ∨ (True → ((False ∧ (True ∧ False)) ∨ p2))))) := by
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
theorem thm_5_vars_233514901382034223142062982859 : ((p1 ∨ (True ∨ p2)) → ((((p2 ∧ True) → (p1 ∧ ((p4 ∧ (p4 ∧ False)) ∧ (False ∨ p5)))) → ((False → p4) ∨ True)) → ((p1 ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53418370896111601119054914772 : ((((((p5 ∧ p2) → True) ∨ (p2 ∧ True)) ∨ ((True ∧ p5) ∧ p1)) → (((p2 → ((p2 ∧ p5) ∧ p3)) ∨ (p3 ∧ (True ∧ p5))) ∨ True)) ∨ p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611435887610988499172146264378 : (((((p1 ∧ (p5 ∨ (((((((False ∧ p2) ∧ (p5 → p1)) → False) → p5) ∨ True) ∨ p5) ∧ (p2 ∨ (p2 ∧ (p4 → True)))))) → False) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724617641775207689798716601251 : ((((p1 ∨ (p1 → True)) ∧ ((p4 → p4) ∧ ((False ∨ (((p4 ∨ p5) ∧ (True ∨ ((False → (False ∧ False)) → p2))) → p2)) → (p2 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647445899421666120022060004450 : ((((p4 → (p5 ∧ (((p5 → (p3 ∨ ((p4 → ((False → (False → p5)) → False)) → (((p1 ∧ p2) ∧ True) ∧ p4)))) ∨ False) → False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112135683425071250861950193741 : (((False ∧ ((p2 ∧ p2) ∧ (((p4 ∨ p2) → ((((p3 ∧ p3) ∨ p5) ∧ p3) → p4)) ∨ (p2 ∨ (p3 ∧ (p5 → True)))))) ∨ p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784074397399197604959774959045 : (((p3 ∨ ((p5 ∧ False) ∨ (((((p1 ∨ False) ∧ (True → p5)) ∨ p3) ∨ p1) ∨ ((False → p1) ∨ (((False ∨ (False ∨ False)) ∨ False) ∨ True))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685638885413317963104701217137 : ((((((True ∧ (((p4 ∨ (p4 ∨ (p4 ∧ p2))) → p5) ∨ False)) → (p5 → (p3 ∧ False))) ∨ p3) → ((p5 ∧ (p5 ∧ (p3 ∨ p5))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62771607517475255801773252028 : ((p4 ∧ (((p2 ∧ (((p4 ∧ ((((p2 ∨ p5) ∧ p1) ∧ p1) ∧ p1)) → p3) → p2)) ∨ ((p3 ∧ True) ∧ p1)) → ((p2 ∧ p2) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51292636891604256657031352927 : (((p5 ∧ ((p3 ∨ ((True → (p4 ∧ (p4 → True))) ∧ (False ∨ (False ∧ (p2 → p2))))) ∨ p1)) ∨ (False → ((p2 ∧ (False ∧ p1)) → p3))) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319537559227043847483508184085 : (p4 ∨ ((((((p5 ∨ False) → (p5 ∨ True)) ∨ p2) → p2) ∨ p2) ∨ ((p1 → (True ∧ False)) ∨ ((((p3 → p1) ∨ p3) → (True ∨ p3)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155244431408207759798747892892 : (((((p5 ∨ p1) → True) ∧ (p4 → (p4 → False))) → ((p4 ∧ (p1 → p4)) ∨ (False → (p2 ∧ p3)))) ∧ ((p4 ∨ ((False ∧ p4) ∨ True)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58556508985335696749243436138 : (((True → True) ∧ (p1 → (((((p5 ∧ True) ∨ False) → (p3 ∨ (((p1 ∨ p1) ∨ p1) ∨ (p4 ∧ (p1 → (p4 ∨ p2)))))) → False) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652119313292314111293309019494 : ((((p1 ∧ (((p5 ∧ True) ∨ (p3 ∨ (p5 ∧ (((False ∧ (True ∧ p3)) → (p4 ∨ (p4 ∧ p4))) ∧ p4)))) ∧ (p1 → p5))) ∧ (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809809192062126247485889269728 : (((p5 → ((p3 ∨ ((p1 ∨ ((((p4 ∧ False) → p1) → (True ∨ p5)) → (False ∨ (p4 ∨ (p1 → (p3 ∧ p4)))))) ∨ p3)) ∨ (p5 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116479873894719226929959133051 : (((p1 ∧ p4) ∧ (((p2 ∧ p3) → p3) → (p1 ∧ (((p1 → p4) ∨ (p3 ∧ ((p5 ∨ ((p1 ∨ p5) → True)) ∧ p3))) ∧ p4)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710525308743687287166594773124 : (((((p3 → ((p2 → p1) → p4)) → p3) ∧ (((((p1 ∧ p5) ∨ (True ∧ True)) ∧ (p3 ∨ ((p5 → False) → False))) ∧ (p4 ∧ p4)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117661441452524906161956776500 : ((p3 ∧ ((p5 ∨ ((True → ((p1 → p4) → p3)) ∧ (((((p4 ∨ True) ∨ p3) → p5) ∧ p1) ∧ p1))) ∨ ((p5 ∨ p5) → p3))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138892402400599056485921207132 : (((True → ((((p2 ∧ p3) ∨ p5) ∧ p5) → (((((p5 → p4) ∧ (False ∧ p4)) → p5) → (False → p1)) → p2))) ∧ p5) → ((p5 → p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 ∧ p3) ∨ p5) ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((((p5 → p4) ∧ (False ∧ p4)) → p5) → (False → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802054170166160967680598064651 : (((p2 → ((p4 → p1) → ((((p1 ∧ False) → True) → (p4 ∧ ((p3 ∨ (True ∧ ((p5 → (True ∨ p5)) ∧ (False → p1)))) ∨ p5))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56403517418015764139130214941 : ((((p1 ∨ (True → True)) → p2) → (((p3 ∧ p3) ∨ (True → (p2 ∨ False))) ∧ ((p2 ∧ ((False ∨ p4) ∧ ((p3 → p1) ∧ False))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177940831316741411260349374401 : ((((False ∨ (True ∨ False)) ∧ (False ∨ ((True ∧ p3) ∨ (p2 → p3)))) ∨ p2) ∨ ((True ∨ ((False ∨ p1) ∨ p1)) ∨ (((p1 ∧ p5) ∨ p2) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243762086553625233951182870562 : ((p5 → p5) ∧ ((((p2 ∨ ((False ∨ (((p5 → ((False ∧ (((p5 → False) ∧ p4) ∨ p4)) → p2)) ∨ p2) ∨ p2)) → p5)) ∨ p5) ∧ False) ∨ True)) := by
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
theorem thm_5_vars_621357395674189042935127650568 : ((((True ∧ ((p5 → True) → (p4 → ((p4 ∧ p2) ∧ ((((p2 ∨ (((p4 ∧ (p2 ∨ p3)) ∧ p5) → False)) → p5) → False) ∧ False))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171823948708947969354263659006 : ((((p2 → ((p3 ∧ True) ∧ p2)) ∨ ((p4 ∨ p3) → ((p4 ∨ False) → False))) → p5) ∨ ((((False ∨ p1) ∧ False) → (p3 ∨ p2)) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704969584194350969139511272477 : ((((True → (False ∧ ((((p3 ∨ p4) ∧ p5) → p4) ∧ p4))) → (p4 → (p1 ∨ (p5 ∨ ((p4 ∧ (p1 ∧ False)) ∨ ((True → False) → p3)))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48522828159865128695534051605 : ((((((p5 → p2) ∧ p1) ∨ ((((p2 ∧ p3) ∨ (True ∨ (p3 ∧ p4))) ∨ (False → (p1 ∨ p3))) → p3)) ∨ p2) ∧ ((p2 ∨ p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753603452356928100921762755266 : (((False ∧ ((p3 ∨ (p4 ∧ (p2 → ((p1 ∨ p4) → (p2 ∨ (((p2 ∨ p3) ∧ p5) → p1)))))) ∧ (((True ∧ False) ∨ (p4 → p3)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736677247785531307844135677095 : ((((p2 → True) ∧ (True ∧ ((((p4 → p1) → (((p3 ∧ p5) → p2) → (p3 → (((p3 ∨ (True → False)) ∨ p2) ∨ p5)))) → False) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64564054101474910481094406993 : ((p1 ∨ (((False → False) → True) ∧ (((((((p5 ∧ (True ∧ (p1 ∧ True))) → ((True ∧ p4) ∨ p5)) ∧ p1) ∨ True) ∧ p4) ∨ p5) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40712688916476569630112811939 : (((((((p4 → False) → p3) ∧ ((p3 ∧ p5) ∨ (p1 → p5))) → ((p1 ∨ (p2 ∨ ((p5 → p2) ∨ (p4 ∧ p2)))) → True)) → p2) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352350045964724822000727097756 : (p4 → ((True ∨ (p3 → True)) ∧ (((p5 ∨ (True → (False ∧ (((False → p2) → (p3 ∧ (False → (p5 ∨ (p1 → True))))) ∨ p4)))) ∨ p2) ∨ True))) := by
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
theorem thm_5_vars_190927292609337296223372586670 : ((((p3 ∨ (p2 ∨ p4)) ∨ p2) ∧ ((False ∧ p1) ∧ p3)) ∨ (((((p3 → ((p1 → p3) ∨ (p3 ∨ p3))) ∨ p3) → p2) ∨ (False → p3)) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111381132158596110640318809124 : (((False ∨ ((p5 ∨ ((((p3 ∧ p3) ∨ (((p2 ∧ (p2 ∨ p2)) ∧ True) ∨ p4)) ∨ ((p4 → p5) → False)) ∧ p3)) ∨ p1)) ∧ p4) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323298805864666455418704166061 : (p5 ∨ (((((p5 ∨ ((p4 → ((True ∧ p4) → p3)) → p1)) → (False ∨ p4)) ∨ (((True ∧ p2) ∨ p4) ∨ (p1 → True))) ∨ True) → (p3 → p3))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38954120704475553150349231638 : ((((p3 ∨ (p2 → p3)) → (((p1 ∧ p2) ∨ False) ∧ ((True ∨ (p5 ∨ (((((True → p2) → p5) ∨ p4) ∧ p3) ∧ p4))) ∨ p3))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_499537291489094925847166878947 : (((((False ∧ p3) ∨ p2) ∨ ((p3 → ((p5 ∨ ((p5 ∨ p1) ∨ p2)) ∨ p4)) ∨ (p3 → ((True → p2) → ((p1 → (p3 ∧ True)) → p3))))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60399178473720889617952721185 : (((p3 → p5) → (((p4 ∧ True) ∨ p3) → ((((p1 ∨ p1) → ((p1 → ((p5 ∧ (p2 → p5)) → (False ∨ p3))) ∨ p4)) ∧ p3) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172001487467901596117724342204 : (((((True ∨ ((p5 ∧ p2) ∧ p1)) → (p2 ∧ (False ∨ p2))) → p1) ∨ (p5 → True)) ∨ ((True ∨ ((p3 ∧ (p5 ∧ (p2 ∨ p5))) ∨ p5)) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808180968971821402370147220822 : (((p4 → (p3 ∧ (((p5 ∨ ((p1 → False) ∧ p1)) → ((p2 ∨ (p4 → (((p2 ∨ False) ∨ (p4 ∧ p5)) ∧ p5))) ∨ p5)) ∧ (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774200048838317491651733936947 : (((False ∨ ((((p4 ∨ (((((p5 → p5) → True) ∧ (p5 ∧ p1)) ∨ (p1 → p5)) ∨ p5)) ∧ True) ∧ (p4 → True)) ∧ (p5 → (p4 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707007921100099628909545983792 : (((((p4 ∧ ((p5 → p2) → (p5 ∧ False))) ∨ True) ∨ (p2 → (p2 ∨ ((p4 → p2) → (p4 → (p5 ∧ (p2 → ((p1 ∨ p3) ∨ p2)))))))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_228201042588116007034679669281 : ((p5 ∧ (True ∨ p2)) ∨ ((((p5 ∧ ((p5 → (p3 ∨ p5)) → p3)) ∨ p5) ∨ ((False ∧ (p3 ∧ True)) ∨ (p1 → p1))) ∨ ((p1 ∧ p4) ∧ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338719546977555781478107911460 : (p1 → ((False → False) ∧ ((False ∨ p5) ∨ ((((p4 → p1) → (True ∨ (p1 ∧ (p3 ∨ True)))) → ((p3 → False) ∨ p4)) → ((True → False) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57776832782463359092325090195 : (((True ∧ (False → p1)) → (p2 ∨ (False ∨ ((((p3 ∧ True) → True) ∧ p1) ∧ (True → (((p2 ∧ p1) ∨ p5) ∨ (p5 ∧ (p4 ∧ p4)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776025654326586184279949574972 : (((False ∨ (p3 → (p4 → ((True ∨ (True ∨ (((p4 ∨ (((True ∧ False) → True) ∧ p2)) → True) ∨ p1))) → ((p5 ∨ p3) ∧ (False ∨ p4)))))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180609516325330079853542473643 : (((((True ∧ p1) ∧ p5) ∨ (p5 → p3)) ∧ ((p3 ∨ True) ∧ (p1 → p3))) → ((p5 ∨ False) → ((True → p5) → ((p2 ∧ (p3 ∧ p5)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h6.left
      let h13 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h17 := h6.left
      let h18 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
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
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347309636354386027537615856569 : (p3 → (((((False ∧ False) → (p3 → p5)) → (p5 → p5)) → False) → ((((p2 ∧ p1) ∧ p2) ∧ (p3 → False)) → (p4 ∨ ((p5 → p2) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h10
  -- False on the left can always be used.
  apply False.elim h11



