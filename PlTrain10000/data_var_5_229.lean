variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780781123975795744209402119405 : (((p2 ∨ (((p4 ∧ (True ∧ p1)) ∨ True) ∧ (((False ∨ (p1 ∨ p3)) ∧ ((p5 ∨ p5) ∨ ((p1 → (p2 ∧ (p3 → False))) ∧ p1))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323188277787794605540991579964 : (p5 ∨ (((((p4 → (((p3 ∧ p1) ∨ p2) ∨ True)) ∧ ((p4 ∧ False) → ((True → (p3 → p1)) ∧ (False ∨ False)))) ∨ p4) → p4) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329120303175950282279734041949 : (True → (((p2 → p1) ∨ (p3 ∧ True)) ∨ ((p1 ∧ ((True ∧ (p1 → p4)) → p2)) ∨ (p3 ∨ ((p1 ∧ p3) → (False ∨ (p1 ∨ (False ∨ False)))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665500000457582949993251815576 : (((((((True ∨ (((p1 → p3) ∨ (((False → False) → (p1 ∨ p3)) → p4)) ∧ (p4 → p5))) ∧ p4) → False) ∨ False) ∧ (True → (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306047372570133710192740480564 : (p1 ∨ (((False ∨ p2) ∧ (p2 → False)) → ((p3 ∨ ((p1 → ((p4 → p1) ∨ False)) → (((p5 ∧ (p4 ∨ p5)) ∧ (False → p5)) ∨ p5))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116436733226463830184629840786 : (((p2 → (False ∧ p2)) → ((False ∧ ((p1 → p1) ∧ (((p5 ∨ p3) ∨ (p2 ∧ True)) ∧ (p3 ∧ False)))) ∧ (p5 → (p4 ∧ p3)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606360958523451118929891596955 : ((((((((((True ∨ (p1 ∨ True)) ∧ ((((p1 ∧ p4) → p1) → True) → p4)) ∨ p1) ∨ False) ∧ ((p2 ∧ p4) ∧ p5)) ∨ True) ∧ True) ∨ False) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149588446297458032402710104350 : ((p3 ∧ (((p2 ∨ (p3 ∧ ((p4 ∧ ((True → ((False ∧ (False ∧ True)) → p4)) ∨ p4)) ∨ p4))) → p3) → False)) ∨ (p5 → (p4 → (p4 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193800365521237754697507510435 : ((p4 ∧ (False → ((((p4 ∨ True) ∨ p4) → p1) → p1))) → ((True → (p5 ∧ (p2 ∨ (((False → p2) → p5) ∧ (p3 ∧ p1))))) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208729311516281756470321225316 : ((p1 ∧ ((p1 → True) ∧ (p5 → p3))) → (((((False ∨ p1) ∨ p4) ∨ p4) → (((p5 → False) ∨ ((False ∨ (p4 ∧ p1)) → False)) ∧ p5)) ∨ p1)) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118844768746490807805948207292 : ((True → (((p1 ∧ (((p4 ∧ p4) → p5) → (p3 → (p1 ∨ p5)))) ∧ ((True ∨ p5) → p2)) ∧ (p2 → (p5 → (p3 ∨ p1))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677275147665470149348384431453 : (((((((p2 → p2) → p3) ∨ (False ∨ ((p4 ∨ (p4 ∧ (True ∧ p2))) ∨ (True ∨ (p3 → p2))))) ∧ p5) ∨ (p2 → ((p1 → p4) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164933664193371404835694405345 : ((((p1 ∧ (((p5 ∧ p5) ∨ p1) ∨ ((p2 → (p1 ∨ p3)) ∧ (p4 ∧ p1)))) ∨ p2) → p3) ∨ ((p2 → (True → (p2 ∨ p2))) ∨ (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218825924429737192980966299349 : ((p2 ∧ ((p1 ∨ p4) ∧ p4)) → (p3 ∨ ((p5 ∨ (False ∨ (p3 ∨ ((p1 → (p4 ∨ (False ∨ (p3 → p1)))) ∨ ((False ∨ True) → False))))) ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326895592957038858529838154540 : (True → (((p1 → ((p1 → ((p2 ∨ (((p5 → (p4 ∧ False)) → p3) ∧ (((p2 ∧ (True → p4)) ∨ p5) ∨ p2))) ∧ p2)) ∨ True)) ∨ False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323241045180709788920747591660 : (p5 ∨ (((p3 ∧ p4) ∧ (p5 ∧ (((((False ∨ (p1 ∨ ((p1 ∨ p1) ∧ False))) ∨ (p2 ∧ p4)) ∧ (p1 → p2)) → p1) ∧ False))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55404136758399011231403279308 : ((((((p2 ∧ True) ∧ p3) ∨ True) ∨ False) → (((p1 ∨ (False ∧ (p2 ∧ False))) ∨ ((p1 ∨ (p5 ∧ p2)) → (p3 ∨ True))) ∧ (p5 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111969900218862577751461081377 : (((((p5 → p3) ∨ (p1 ∨ (p1 ∧ False))) ∧ ((p3 ∨ False) ∧ ((p2 ∨ ((False ∧ ((p1 ∨ False) ∧ True)) ∨ False)) ∨ p3))) ∨ p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733421638466965543071892082251 : ((((p4 ∧ p1) ∧ ((((((p1 → p4) → ((p3 ∧ (((((p4 ∨ p2) → False) → True) ∧ False) → p1)) ∧ True)) ∧ p1) → False) ∨ p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315925950678337397632355419156 : (p3 ∨ (True ∧ (p3 ∨ (((p4 ∧ ((((p4 ∨ p3) → p4) ∨ False) ∧ p2)) → (p3 ∨ p5)) ∨ ((False ∧ ((p1 ∨ False) ∧ True)) → (p2 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117931207924849153155739259156 : ((p5 ∧ ((p2 ∧ p5) ∨ (p1 ∧ (((((p5 ∧ (p5 → p1)) ∨ (p3 ∧ p2)) ∧ p1) ∧ p2) ∨ ((p1 → p3) ∨ (True ∧ p1)))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171347679589361399142279348795 : (((((p5 ∧ p3) ∨ ((p1 ∨ p1) → ((p2 ∨ False) ∨ (False ∨ p2)))) → p5) ∧ p5) ∨ (((p2 → p2) ∧ False) → (((p2 ∧ p1) ∨ p4) ∧ False))) := by
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
theorem thm_5_vars_60358588405256928050424394822 : (((p2 → p5) → (((p5 → (True ∧ (False → p2))) → (p1 ∨ ((True ∧ (False → False)) ∨ (p3 ∨ p1)))) ∧ (((p5 ∨ True) → p5) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102828222815725631374242397459 : (((((p3 ∧ ((((p1 ∨ p3) → (p5 ∨ (p4 ∧ (p5 → (False → p1))))) ∨ (False → p2)) ∨ p4)) ∧ p5) ∧ (p1 → True)) ∨ True) ∧ (p4 ∨ True)) := by
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
theorem thm_5_vars_764077428506754863874715979252 : (((p3 ∧ (p2 → (False ∨ ((p4 ∧ ((((False → (p4 → False)) → (((p5 → p5) ∧ p4) → p2)) ∨ p2) ∨ (p2 ∧ p5))) ∧ (False → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218901169799852648169581733972 : ((p3 ∧ ((p5 ∧ False) ∨ p2)) → ((((p2 ∨ True) → ((((p2 → p3) → p5) ∨ p4) ∨ ((p3 ∨ False) → ((False → p3) ∨ p5)))) → False) ∨ p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263626399169570891168410741410 : (True ∧ (((p5 → p5) → ((((True ∨ (p2 → False)) ∨ p3) ∧ ((p1 ∨ (p2 → p4)) ∨ (p1 → p1))) → p1)) → ((p2 → p5) ∨ (True ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349941129489427886916213977549 : (p4 → ((((p2 ∧ (p2 ∧ (p1 ∧ (False ∧ (False ∨ ((p5 → p1) ∧ (p2 ∨ (p3 → ((False → p4) ∧ (True ∧ p2)))))))))) ∨ p3) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186898030493532157319923460903 : (((p4 → ((p5 → p2) → p3)) → ((p1 ∨ p2) ∨ (p5 ∨ p5))) → ((False ∨ ((p5 ∧ ((p2 ∨ p4) → p1)) → p2)) ∨ (True ∨ (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208307570402906207009242150853 : (((p5 ∨ p3) ∧ (p3 ∨ (p1 → p3))) → (p2 ∨ (p1 → ((False ∨ ((p2 ∨ p5) → p5)) → (((p1 → p3) → ((True → p5) ∨ p1)) ∧ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
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
        -- One of the premise coincides with the conclusion.
        exact h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h21
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h27
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h28 =>
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h25
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42801809450296192862513674435 : (((p1 → ((((((True ∧ p4) ∨ (True → p4)) ∧ p3) ∨ (((p2 ∨ (p1 ∧ (p5 ∧ False))) → p1) ∧ p2)) ∨ (p2 ∧ p1)) ∧ p1)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2806454266201406199113795564 : ((p2 → ((False → False) ∧ False)) ∨ (((True ∧ ((p2 ∨ ((p1 ∨ True) ∧ p4)) ∧ True)) → (False ∧ (p4 ∧ p3))) ∨ (p3 ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_230723383046279623406513131544 : (((p5 → False) ∧ True) → (((p2 ∨ (p3 ∨ (((p3 ∧ p1) ∨ p4) → (p2 ∨ (p1 ∧ False))))) ∧ (p2 ∨ (p2 ∨ (p4 ∧ True)))) → (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h1.left
        let h15 := h1.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h16 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h17 := h14 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h1.left
        let h22 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h1.left
        let h27 := h1.right
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h28 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h29 := h26 h28
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h1.left
          let h33 := h1.right
          -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
          have h34 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h32, we can now drive its conclusion.
          let h35 := h32 h34
          -- False on the left can always be used.
          apply False.elim h35
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Conjunctions on the left can always be decomposed.
          let h39 := h1.left
          let h40 := h1.right
          -- One of the premise coincides with the conclusion.
          exact h37
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h42 =>
        -- Conjunctions on the left can always be decomposed.
        let h43 := h1.left
        let h44 := h1.right
        -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
        have h45 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h43, we can now drive its conclusion.
        let h46 := h43 h45
        -- False on the left can always be used.
        apply False.elim h46
      case inr h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Conjunctions on the left can always be decomposed.
          let h49 := h1.left
          let h50 := h1.right
          -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
          have h51 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h49, we can now drive its conclusion.
          let h52 := h49 h51
          -- False on the left can always be used.
          apply False.elim h52
        case inr h53 =>
          -- Conjunctions on the left can always be decomposed.
          let h54 := h53.left
          let h55 := h53.right
          -- Conjunctions on the left can always be decomposed.
          let h56 := h1.left
          let h57 := h1.right
          -- One of the premise coincides with the conclusion.
          exact h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158179052810823129840350899147 : ((((p1 → p3) → (p4 ∨ p3)) → ((p3 → (((p4 ∧ (p1 ∧ p2)) ∧ True) ∧ (p3 → p3))) ∨ True)) ∨ ((p1 ∨ ((p2 ∨ False) ∨ p4)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205517062600588808031639371750 : (((p5 ∧ p4) ∧ ((p4 ∨ True) ∧ p2)) ∨ (p4 ∨ (p5 → (False ∨ ((p5 ∨ ((((p1 ∧ p4) ∨ p4) ∨ p4) ∧ True)) ∨ (p4 ∧ (True ∨ p5))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618925011573516405592646397187 : (((((p5 → (p2 ∨ p1)) ∧ (((False ∨ p1) ∨ (p1 ∨ p5)) ∨ ((((p4 ∨ True) ∨ p1) → (p2 → (p1 ∧ (False → True)))) ∨ p3))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685281140137413373269786404537 : ((((p1 → (p2 ∨ ((((((p2 ∧ (p4 ∧ p2)) ∨ True) ∨ (p1 → False)) ∧ p2) ∧ True) ∧ True))) ∨ (True ∧ ((True → p5) → (False ∨ True)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185497101839940717712569007262 : ((p2 ∨ ((p4 ∨ (p1 ∨ ((p5 ∨ p3) ∨ True))) ∨ (False → p3))) ∨ ((p4 → ((p5 → p4) ∨ (p1 ∧ (True ∧ (p1 ∧ p4))))) ∧ (True ∧ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209101847329412177732069548638 : ((p2 ∨ ((True ∨ p4) ∧ (p4 → True))) → ((True ∨ (p3 → True)) ∧ (p5 ∨ (True → (p1 → ((p2 ∧ p3) → (p5 ∨ ((p3 ∨ p4) ∨ False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177802398656163205801510126307 : (((p4 ∨ ((((p2 ∧ ((p4 ∨ False) → False)) ∧ True) ∨ p5) ∧ p3)) ∧ p3) ∨ (((False ∧ True) ∧ False) → ((False ∧ (p3 → False)) ∧ (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49047978847807140811967334982 : (((((((p5 → p5) → (True ∨ ((p3 ∨ (p1 ∨ (p3 → (p4 → p5)))) ∧ True))) ∧ p4) ∨ p5) ∧ (p5 ∨ p1)) ∨ ((p4 ∧ True) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56139199861994033882047366813 : ((((True ∨ True) → (p4 ∨ p5)) ∨ ((((p1 → False) → (p2 → ((p2 → ((False ∧ False) ∨ (p3 ∨ (True → False)))) ∨ p2))) → False) → p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → False) → (p2 → ((p2 → ((False ∧ False) ∨ (p3 ∨ (True → False)))) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44722868479279824175612672066 : ((((((p3 ∧ p2) ∨ p4) ∧ p1) ∨ ((p5 → (p4 ∧ (p1 ∨ True))) ∧ (((p2 ∨ p3) ∧ (True → ((False ∨ p3) ∨ p2))) → False))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115234258516105705447154285370 : ((((p4 ∧ (p4 → (p1 ∨ (p5 ∧ (p5 → False))))) ∨ p2) ∨ (((p4 ∨ (p2 → p2)) ∨ ((False → p5) ∨ p3)) ∨ (False ∧ True))) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620943966667171128521738836512 : (((((p4 ∨ p3) → ((((((p4 → p2) ∧ False) ∧ ((p3 ∨ False) ∨ p1)) ∨ (p4 ∨ p5)) ∧ (True ∧ p3)) ∨ ((False ∨ p4) → p3))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340832882788869894985950823424 : (p2 → ((((((((((False → (True → False)) ∧ False) ∧ False) ∨ p2) ∧ p2) ∧ (False ∧ p3)) → p2) ∨ (p4 ∨ (p3 → False))) → (p4 ∨ p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709668868265460111673821901913 : ((((p4 ∨ ((p1 ∨ p1) ∨ ((p2 ∨ p4) → False))) → (((True ∧ p1) ∨ p4) ∧ (((p3 ∧ True) → (p4 ∨ (p4 ∧ (p5 ∧ p4)))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190075387653779462863897456350 : ((((True ∨ (((p2 → p4) ∧ True) ∧ p3)) → p2) ∧ p5) ∨ (p4 → ((False ∧ p3) ∨ (((((p4 → p1) ∧ (p3 → p1)) → p5) → True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49402856412638356289675077720 : ((((((p4 ∧ p4) ∨ (p4 ∧ p5)) ∧ (p2 ∧ ((p3 ∨ (p3 → (p3 ∧ ((p4 ∨ p2) ∧ p3)))) ∨ p4))) ∧ p1) → ((False ∨ p5) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213462939385310036359596841252 : (((True → (p3 → False)) ∧ p2) ∨ (((p1 → (p4 ∧ True)) → (((True → True) → (p3 ∨ (p2 ∨ (p1 → True)))) → (True ∧ (p4 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134530050668534170957018538976 : ((((((p2 → p1) → (((True ∨ False) ∧ p3) ∨ ((True → ((False ∨ p3) ∨ (p1 ∧ False))) ∨ p2))) ∨ p5) → p3) → p4) ∨ ((p3 ∧ p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135773963318642033447584144866 : (((((True → p2) ∧ (((p4 ∨ p2) → ((False ∨ True) ∨ True)) ∧ p2)) ∨ p1) → ((((False → p3) → p2) ∧ p1) ∨ p1)) ∨ (False → (p2 ∧ p4))) := by
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
theorem thm_5_vars_57649834412991025298090376244 : ((((p1 ∨ p3) ∨ p1) → (p4 → (p5 ∨ (((((p3 ∨ p4) ∨ (((True ∨ (False ∧ (True → p2))) ∧ p3) → p3)) ∧ p2) → False) ∨ p4)))) ∨ p4) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136730481870461347746095458415 : (((p5 ∧ p4) ∧ ((False ∨ ((p4 → True) → (p3 ∧ (p2 ∧ ((p2 ∨ True) → (True ∨ ((p2 → p5) ∧ p1))))))) → False)) ∨ ((p5 ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62517873749295020071890206927 : ((p3 ∧ (p4 ∧ (((False ∨ p1) → (p5 → ((p3 ∧ (p5 ∧ ((True ∨ p3) ∨ True))) ∧ (p3 ∨ True)))) ∧ (p3 ∧ (False → (p3 → p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186964280312303122910495048646 : ((((p1 → False) → True) ∨ (((True → (p1 ∧ p4)) → p3) ∨ False)) → ((((p1 → p4) ∨ p2) ∨ ((p5 ∨ (p2 ∨ True)) ∧ (p3 ∨ p5))) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689982286052142025721282368494 : ((((p1 ∧ (((p3 ∧ p5) ∨ (((p2 ∧ p4) → (False ∧ False)) ∧ p3)) ∧ (True → p4))) ∨ ((True ∨ p5) ∨ (True ∨ (p5 ∧ (p4 ∨ p5))))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_42414220782167650031782269362 : (((p5 ∧ ((p3 → ((p5 → (p1 → (p5 ∧ ((((True → p4) → (p2 → False)) ∧ (p2 ∧ p3)) ∨ False)))) → (False ∨ p5))) ∨ p3)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196873848673219451969573158402 : (((p5 ∨ (p1 ∧ (p1 ∧ (p4 ∧ True)))) ∧ p2) ∨ (False → (((p4 ∨ p5) ∧ p3) ∨ (((((False ∧ True) ∨ (p5 ∨ p5)) → p2) ∨ p3) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64100696673035914633822208646 : ((False ∨ ((((p3 ∨ (p3 → p3)) ∨ p3) ∧ (p3 ∧ (p1 ∧ p3))) → (((p5 → (p4 ∧ (p4 → p4))) → ((p4 ∨ False) ∨ p3)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314742438817235023729070315372 : (p3 ∨ (((False ∧ (p3 ∧ (p2 → (False ∧ ((p3 ∧ p4) ∧ p2))))) ∧ (p2 ∧ False)) ∨ ((p4 ∨ ((True ∨ (p4 ∨ (p3 ∧ p5))) → p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52172489945706171786100490939 : (((((p5 ∧ (p4 ∨ p4)) ∨ (p5 → p4)) ∧ ((False ∨ ((p4 → p2) ∧ p4)) ∨ True)) → ((((p1 ∨ (p2 ∧ p1)) ∧ p2) ∨ True) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249034596666975501106758294996 : ((p4 ∨ False) ∨ (True → ((p5 → ((True ∧ ((p3 ∧ (p4 ∧ ((p3 ∧ p5) ∨ p1))) ∨ p2)) → p2)) ∨ ((False ∧ ((p4 → True) ∧ False)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201959898453546789603920729747 : (((p5 ∨ ((p3 ∧ p3) ∨ True)) ∨ p4) ∧ ((p1 ∨ (p1 ∧ p2)) → (p5 → (((p2 ∨ p4) ∨ p4) ∨ ((False → (p1 → p5)) → (True → p1)))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336611385226957733097219394358 : (p1 → ((((((False ∨ True) ∧ p4) ∨ ((p2 ∨ ((p2 ∨ p3) ∧ p3)) ∨ ((p5 → p1) ∧ ((True → p1) ∨ False)))) → p5) ∧ (False ∨ p1)) → p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (((False ∨ True) ∧ p4) ∨ ((p2 ∨ ((p2 ∨ p3) ∧ p3)) ∨ ((p5 → p1) ∧ ((True → p1) ∨ False)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314781372337135149025520546700 : (p3 ∨ (((True ∨ p5) ∧ (p5 → ((True ∧ p2) ∧ (((False ∨ p1) ∨ p4) → p3)))) → ((False ∨ True) ∧ ((p2 ∧ (True → (p4 ∨ p1))) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149110458928488254146330662833 : (((p5 → (p2 ∨ p1)) → ((p5 ∧ (((p5 → (p4 → p3)) → p3) ∧ ((True ∧ True) → p5))) → (p4 ∨ p4))) ∨ (((p3 → True) → False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47501236519204684255541069301 : (((p1 ∨ ((p5 ∧ p3) ∧ (((((True → (((False ∨ p1) ∨ (False ∨ (False ∨ p3))) → p3)) ∨ p5) ∧ True) → p5) → p2))) ∨ (p2 → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698715047552398083776371262124 : (((((p5 ∨ p2) ∧ (False ∧ (((p2 ∧ True) ∧ (False ∧ p2)) ∨ p3))) ∨ (((p2 → p4) ∨ (p3 ∨ (p2 ∧ (p5 ∨ False)))) → (False → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18909086790791579468642582453 : (((True ∧ ((((((p1 → (True ∨ (p2 ∨ (p2 → p4)))) ∧ p5) → p1) → p5) → p4) ∧ p2)) ∨ (((p2 ∨ False) ∧ p4) → (False ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231745169149503837232579474299 : (((p3 ∧ True) → p4) → ((True ∧ (((p2 ∨ p1) ∨ p2) ∨ (False ∨ ((p4 ∨ ((((p2 → p3) → p4) → p5) ∨ True)) → p4)))) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315157420633784149460298758416 : (p3 ∨ (((p3 ∨ (p3 ∨ False)) ∧ (True → False)) → ((((p5 → (((True ∧ p4) ∨ p3) ∧ p2)) ∧ ((False → False) → p5)) ∧ p2) ∧ (False ∨ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h24 := h21 h23
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h27 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h28 := h21 h27
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- False on the left can always be used.
      apply False.elim h29
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h32 =>
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h33 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h34 := h31 h33
    -- False on the left can always be used.
    apply False.elim h34
  case inr h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
      have h37 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h31, we can now drive its conclusion.
      let h38 := h31 h37
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- False on the left can always be used.
      apply False.elim h39
  -- Conjunctions on the left can always be decomposed.
  let h40 := h1.left
  let h41 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h40
  case inl h42 =>
    -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
    have h43 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h41, we can now drive its conclusion.
    let h44 := h41 h43
    -- False on the left can always be used.
    apply False.elim h44
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h46 =>
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h47 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h48 := h41 h47
      -- False on the left can always be used.
      apply False.elim h48
    case inr h49 =>
      -- False on the left can always be used.
      apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205857228066928602380554992016 : (((p4 → p1) → ((True ∧ p3) → p4)) ∨ (((((p5 ∧ ((False → p5) ∧ p2)) ∨ (False → True)) ∨ p1) ∨ p1) ∨ ((False → p2) → (p5 ∧ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324805757969932921364566024666 : (p5 ∨ ((True ∨ p1) ∧ (((((p4 ∨ False) ∨ True) → ((p5 → ((p1 → (p5 → p2)) → (p1 ∧ (p1 ∨ p1)))) ∧ (p4 → p1))) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_114515499164852364987421218113 : ((((p4 → p1) → (((p1 ∨ (p4 ∨ (((False → (p5 ∧ p1)) → p3) → p4))) ∨ p4) ∧ p5)) → ((p5 ∧ (p5 ∧ p4)) → p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152170204559473166651966285079 : ((((((p3 ∧ (True → p1)) ∨ True) ∧ p1) ∧ False) → ((False → True) → (((p4 → False) ∧ (p5 → p1)) ∨ False))) → ((p1 ∨ (False ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214651863203795107426224698919 : (((p2 → p4) ∧ (p3 ∧ True)) ∨ ((True ∧ ((p4 ∧ p1) ∨ ((True → p3) → (p5 ∧ True)))) → (((p5 ∨ p4) ∨ ((p1 ∨ p3) ∨ True)) ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196676519037819614657735348134 : ((((((p5 ∨ p3) ∧ p1) ∧ p1) ∨ p5) ∧ p5) ∨ (((True ∨ p5) ∧ (((True → (p3 → p4)) ∨ (p5 → (p1 → (True ∨ p2)))) → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310391795335174557214043028582 : (p2 ∨ (((p1 ∨ ((True → False) ∨ p2)) ∧ (p1 ∧ p2)) ∨ (((p5 → False) ∧ ((p5 ∧ p2) ∧ ((p5 ∨ ((p4 → p5) → p5)) ∨ p4))) → p1))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337951706864867864327436634682 : (p1 → (((((p3 ∨ p4) ∧ p1) ∨ p5) ∨ ((p4 ∧ (p2 ∨ p2)) → p5)) ∨ ((p4 → (True → (p1 ∧ (p1 ∨ (p4 → (p5 → p2)))))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133984416485726468409720723574 : (((((p4 ∧ (((p3 ∨ (((p2 → False) → (True ∧ False)) ∧ p2)) ∧ ((p4 ∧ True) → p2)) → True)) → p3) ∧ True) ∨ p2) ∨ (p1 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150651976030708143505710886988 : (((p2 ∨ ((((((p2 → ((p3 ∨ p3) ∨ True)) → (p5 ∨ p2)) ∨ p1) ∨ p2) ∨ False) ∧ (p5 → p1))) ∧ p3) → (p4 → (p1 ∨ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322537389288586850550273503220 : (p5 ∨ ((p5 ∧ (((((p2 → (p1 → p1)) ∧ True) → p5) ∧ ((((p5 ∧ False) ∨ (p3 ∧ ((p3 ∧ p1) ∨ p3))) ∨ True) → p4)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67491080303225735741285225864 : ((p1 → ((p1 → (p3 ∧ (p4 ∧ ((False → p4) → (False ∨ (p2 ∨ True)))))) ∨ (((False ∨ ((p5 ∧ (p4 → p3)) ∨ p2)) ∨ p1) ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_232394699767092339236071651311 : (((p5 → p3) → False) → (p5 ∨ ((p5 ∨ ((p1 ∧ p2) ∨ (p2 → p1))) ∨ (False → ((p1 → ((False → p3) → (p4 ∧ p2))) ∧ (p3 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103448106424577334846916833776 : ((((((p2 ∨ ((p5 ∨ (((p4 ∧ False) ∨ p3) ∧ ((True ∧ p5) ∨ (p2 ∧ False)))) ∨ p4)) ∨ p3) → (p1 ∧ p5)) ∧ p3) → p1) ∧ (True ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ ((p5 ∨ (((p4 ∧ False) ∨ p3) ∧ ((True ∧ p5) ∨ (p2 ∧ False)))) ∨ p4)) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164807248344541689601826616397 : ((((p4 ∨ (p3 ∧ p3)) → ((p4 ∨ False) ∧ (p5 ∨ ((True ∧ (p3 ∨ p5)) ∨ p2)))) ∨ True) ∨ ((p4 ∨ p1) ∧ (p3 → ((p4 ∧ True) → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198599878016155684958522906341 : ((p2 ∨ (((p5 ∧ p5) → (p5 ∨ p4)) → p2)) ∨ (p1 ∨ ((p5 → p5) ∨ ((p2 ∧ (((p1 ∨ (p1 → True)) → p2) → (True → p4))) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217411163354314848667320611326 : (((p1 → (p1 ∧ False)) ∨ True) → ((False ∧ ((False ∧ (p5 → ((((False → p1) ∧ p1) → (p5 ∧ p1)) → (p4 ∨ p1)))) ∧ False)) ∨ (p3 → True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259817258775381175296041579014 : ((p1 → p3) → (((p4 ∧ ((p3 ∨ ((False ∨ (p4 ∧ p4)) → True)) ∨ (p3 ∨ p5))) ∨ p4) ∨ (p1 → (p1 → (p2 ∨ ((p2 ∧ p5) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225084191396097351748050918115 : (((p1 ∧ p5) ∧ False) ∨ ((((p4 → ((p4 → ((p2 ∨ False) ∨ (False ∧ (p2 ∨ (True ∨ (p2 ∧ False)))))) ∧ p1)) ∨ p4) ∨ p1) → (p4 ∨ True))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133798364268216551607202318664 : (((((False → p5) ∧ p2) → ((p5 → p4) → ((p3 ∨ p3) ∨ ((p5 ∨ True) ∨ ((p3 ∨ (p5 ∧ p4)) → p3))))) ∧ p5) ∨ (p4 → (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344310520484496983944941072655 : (p2 → (p3 ∨ ((((p3 ∧ p5) ∧ (((p5 ∧ p3) → True) ∨ p3)) → p2) → ((((p4 ∨ False) → p1) → p1) → ((p2 ∧ (p5 ∨ p1)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703697295317287007642113983201 : ((((((p4 ∨ (True ∨ (p1 → False))) ∧ (p4 ∧ p4)) ∧ p3) → ((p4 ∧ (True ∨ p5)) ∧ ((((p3 → (p5 ∧ p1)) ∧ True) ∨ True) ∨ False))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h5.left
      let h12 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h19.left
      let h26 := h19.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h19.left
      let h29 := h19.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h30.left
  let h33 := h30.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h33.left
    let h36 := h33.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h33.left
      let h40 := h33.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h33.left
      let h43 := h33.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350133183643335944847210433022 : (p4 → ((((p1 ∨ ((((p1 → p4) ∧ p1) ∨ p5) ∨ False)) ∨ ((p5 ∨ p2) → p1)) ∨ ((p4 → (p4 → (False ∨ True))) → (p5 ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225314726819322863627561667763 : (((False ∨ p4) ∧ False) ∨ (((((p1 → (False → p4)) ∧ False) ∧ p3) ∨ (False → (p2 ∧ (p2 ∧ (p4 ∨ ((False ∨ p1) ∨ p5)))))) ∨ (False ∨ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52796841607520186468864403006 : (((((((p2 ∨ p4) ∧ (p4 ∧ p2)) ∧ p4) → True) ∨ (p2 ∧ (p2 ∧ p5))) → ((((p3 → p5) ∨ (p5 → False)) → p1) ∨ (p5 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806828682947293672325178227828 : (((p4 → ((p5 ∧ ((p4 ∨ (True → p4)) ∧ (((p4 → False) ∧ False) ∧ (False ∧ (((False ∧ (p4 ∨ p4)) ∧ p1) ∧ False))))) ∨ (p2 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707375288427982416660356651062 : (((((((p4 → p2) ∧ p1) → p1) → (True → p4)) ∨ (p4 ∧ (p4 ∨ (p1 ∧ (((p4 ∧ ((p5 ∧ p3) ∧ (p2 ∨ p3))) → p2) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152136719855424627566461090446 : (((False → (False ∨ ((p2 → (True ∧ p2)) ∨ p3))) ∧ (p2 ∧ ((((p3 → (True ∨ False)) ∧ True) ∨ True) ∨ True))) → ((p5 ∨ (True → p5)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



