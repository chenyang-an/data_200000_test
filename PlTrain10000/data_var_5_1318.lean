variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149117004036054543949982810758 : (((False ∧ p1) ∧ ((p4 ∧ ((p3 ∧ (((p4 → (p4 ∧ p3)) ∧ True) ∧ ((True → p5) → p2))) ∧ True)) → p1)) ∨ (p3 → ((p3 ∨ p5) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950162930637345976315635956309 : (((((p4 ∨ True) → False) ∧ ((True ∨ p2) → ((p4 ∨ False) → ((True ∧ (p4 → True)) ∨ ((p2 ∨ (p4 → (p2 ∨ False))) ∧ (p2 ∨ p2)))))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67883073122755392212652544607 : ((p2 → ((((p2 → (p5 → ((p3 → (p5 → False)) ∨ p1))) ∨ False) ∨ ((p3 → True) ∧ (p5 ∧ p2))) ∨ ((p4 ∨ False) ∨ (True ∨ p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615451164532533821473079076300 : ((((((((p3 ∨ (((p1 → True) ∧ (p3 ∧ p4)) ∧ p3)) ∨ True) → (p4 ∧ False)) ∧ p4) → (((p5 → (p5 → p5)) ∧ p5) ∧ p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42735525372869747756293739867 : (((True → ((((False ∨ (False → p2)) ∨ ((p1 ∧ p5) → p4)) → (((True ∨ ((p1 ∧ p3) ∧ False)) ∧ p1) ∧ True)) → (p5 ∨ p2))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713861672320930753319222151398 : ((((((p2 → True) ∧ (True ∨ p1)) ∨ p4) → (True ∧ ((True ∨ ((True ∨ (p1 ∨ (True ∨ (p3 → p1)))) → ((p4 ∧ p5) ∨ False))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49591346534363070983230509202 : ((((((p1 ∧ False) ∨ p5) ∧ ((True → ((True ∧ True) → p1)) ∨ p3)) ∨ (True → ((True ∨ p1) ∧ (p2 ∨ True)))) → (p3 ∧ (True ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251790363972762604326834402618 : ((p3 → p4) ∨ (((((p2 ∨ (p2 ∨ (p3 → p2))) ∧ p1) → False) ∨ (((False ∨ p4) ∧ ((p1 ∨ p2) ∨ False)) → (True ∧ p4))) ∧ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    cases h3
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172011928639086033332508384167 : ((((p4 ∧ (((p1 ∨ False) ∧ p4) ∧ p2)) ∧ (p2 → (p5 → p5))) ∨ (False → p5)) ∨ ((p3 ∧ (False ∧ False)) ∨ (p1 ∧ (True ∧ (True → p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2257197376174870687389577298 : (((p4 ∧ (p3 → p5)) → (((p5 → ((p2 ∨ False) ∨ p3)) ∨ True) ∨ p2)) ∧ ((p3 → (p1 ∧ ((p2 ∨ p2) ∧ (p4 → p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224939667405508141072242898572 : ((p5 → (False → p2)) ∧ ((p2 ∧ ((False ∨ (p5 ∧ p2)) ∨ (((p2 → (True ∧ False)) ∧ p1) ∨ (False ∨ p4)))) ∨ (((p2 → p5) → p2) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727760545378375617786073940516 : ((((False ∨ (p2 ∨ p3)) ∨ (((p5 ∧ ((p1 → p4) ∧ p5)) ∨ (p1 → ((p2 ∧ p4) → ((True ∧ (p1 → (p5 ∧ p4))) ∧ p2)))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57666328568139937041440903411 : ((((True → True) ∨ p4) → (p4 → ((p3 ∨ (True ∧ (p4 ∧ p2))) ∨ ((p3 ∨ (p5 ∨ p1)) ∨ (p1 → ((p3 ∧ (False → p5)) ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64979991252087527752003178094 : ((p2 ∨ (((p4 ∨ p4) → (p2 ∨ p1)) ∨ (((p3 → False) → ((p5 ∧ p3) → (((p3 → True) → (p3 ∧ (True ∨ False))) ∧ p3))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264813208795150302915704520704 : (True ∧ ((p4 ∧ p1) ∨ ((((p5 → p3) ∧ (((p3 ∨ p1) → ((p1 ∨ p4) ∨ p3)) ∨ (False → p4))) → (p1 ∧ p5)) ∨ ((False ∧ p4) → False)))) := by
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
theorem thm_5_vars_779386677905473840294447836103 : (((p2 ∨ ((((p1 ∨ (p4 ∨ (((False ∨ ((((False ∧ p3) → p3) ∨ (p3 ∧ True)) ∧ p1)) ∨ True) → (p3 → p2)))) ∨ p3) ∨ p4) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185375809421008952771865124107 : ((p5 ∧ ((True ∧ (p1 ∨ ((p3 ∧ p1) ∨ p2))) ∧ (p4 ∨ p5))) ∨ (p4 → ((True → p3) → ((p3 → (False ∧ (p3 ∨ (p3 ∧ True)))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937421886248961009408475341616 : (((((False ∧ p5) ∨ ((True ∧ p3) → False)) ∧ (p3 ∧ (p3 → (((p1 ∨ (p3 ∧ p1)) → (((p1 ∧ (p5 ∧ p4)) ∧ True) ∨ p4)) ∧ p2)))) → p1) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (True ∧ p3) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51758067813741870278982150146 : ((((p2 ∨ p2) ∨ ((((p1 → (p3 → False)) ∨ p1) → p3) ∧ ((p1 ∧ False) ∨ False))) ∧ (p3 → ((p4 ∧ ((p5 → p5) → p3)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134596274279698374386990539697 : ((((((p4 ∨ (p1 ∧ False)) ∧ ((p2 ∨ p3) ∨ (p4 ∨ (p3 ∨ p4)))) ∧ (False ∧ (p1 → False))) → (False ∧ True)) → p5) ∨ (False → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69140223488054518135451628271 : ((p5 → ((((p3 ∨ ((p3 → (((p3 ∧ p4) → ((True ∧ False) ∧ True)) → (True ∧ p1))) → False)) ∨ p2) ∨ True) ∨ (False → (True ∧ p2)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119231609477480971493547718227 : ((p2 → ((p5 ∨ p4) ∨ ((p4 ∨ p3) → (p1 → (((False → ((True ∨ (p3 → (False ∧ True))) → (p3 → p2))) → p4) ∨ p3))))) ∨ (p3 ∨ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18802740234517002249463052425 : ((((((p4 ∨ True) ∨ (p2 ∧ p2)) ∨ ((False → p2) → (p1 ∧ (p2 ∨ False)))) ∧ (p5 ∨ p2)) ∨ (((False ∧ p3) ∧ True) ∨ (p4 ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_609899271812296934640842571272 : (((((p3 → (((p1 → ((p4 ∨ (p2 → p3)) ∧ p2)) → ((p4 ∨ (p2 ∧ (p2 ∨ ((p5 ∨ p2) → p1)))) ∨ p4)) ∨ True)) ∨ p1) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_786484809511619823184475122983 : (((p4 ∨ (((((False ∨ (p5 → (p5 → p2))) ∨ False) ∧ p5) ∧ (p2 ∨ p2)) ∨ ((False ∨ ((False ∧ p4) → p5)) ∧ (p3 → (p5 ∨ p3))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41058266923771069379327819730 : ((((True ∧ ((p4 ∧ (((((p2 → ((p3 ∨ p2) → p5)) ∧ False) ∨ p2) ∧ p3) ∨ (False → p5))) ∨ (p3 ∧ p3))) → (p1 ∧ p2)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112213028488421051310004062471 : (((False ∨ ((p2 → p1) ∧ (((((p5 ∧ False) ∨ True) ∧ False) ∧ p3) ∨ (p1 → (((p1 ∧ (p1 ∨ p3)) ∧ p5) ∨ p3))))) ∨ True) ∨ (False ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165219301983410551102482100457 : ((((((p3 ∧ (p5 ∧ False)) ∧ p2) ∨ p4) ∧ ((True → (p5 ∨ True)) ∧ p2)) ∨ (False → True)) ∨ (p5 ∨ (((p1 ∨ (True ∨ p4)) ∧ p2) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_952319785330854330724651179142 : (((((p3 ∨ p5) ∧ p1) ∨ ((((False → (p2 ∧ (True ∨ p3))) → (((True ∨ p5) ∧ p5) ∨ True)) → (p3 ∧ False)) ∧ (p4 ∧ (p5 ∨ p2)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h13 : ((False → (p2 ∧ (True ∨ p3))) → (((True ∨ p5) ∧ p5) ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h13
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h18 : ((False → (p2 ∧ (True ∨ p3))) → (((True ∨ p5) ∧ p5) ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h20 := h8 h18
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337942158833699128391742731245 : (p1 → ((((False ∨ p3) ∨ (((p1 ∧ False) ∨ p3) ∨ (p3 ∧ True))) ∨ False) ∨ ((p3 ∧ ((p2 → p5) → (p2 → (p4 ∧ p2)))) ∨ (False → True)))) := by
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
theorem thm_5_vars_668419284104679079371935910164 : ((((((((p1 → (p1 ∨ p5)) ∧ True) ∧ ((True ∧ (p2 ∧ False)) ∨ (((p1 → p5) ∨ p3) → False))) ∨ p4) ∧ p5) ∨ ((False → False) ∧ True)) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190134531944078465987362949023 : ((((p2 ∨ p1) ∧ (True ∧ ((p3 → p5) → p1))) ∧ True) ∨ ((p2 ∨ ((False ∨ ((((p1 → p5) ∨ True) ∧ p1) ∨ p3)) → p3)) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736194104247048892370578367953 : ((((False → p1) ∧ ((p4 → (p3 ∨ ((p4 ∨ ((p4 → p1) ∧ ((False ∧ p2) → False))) → p3))) ∧ (p2 → (((p2 ∨ p3) → False) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655625931764866196664094578433 : (((((True → ((((((p4 → p5) → p5) ∧ p4) → False) ∨ ((p3 → (p5 ∧ p2)) ∧ (p4 ∧ True))) → p4)) → (p5 → p1)) ∨ (False → p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314456908955000352033065635026 : (p3 ∨ (((((((True ∧ p5) → (False → (True → (p3 → p3)))) ∧ p1) ∨ (p1 → p5)) ∨ (False → True)) → False) → (False ∧ (p5 ∧ (p2 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True ∧ p5) → (False → (True → (p3 → p3)))) ∧ p1) ∨ (p1 → p5)) ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((((True ∧ p5) → (False → (True → (p3 → p3)))) ∧ p1) ∨ (p1 → p5)) ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((((True ∧ p5) → (False → (True → (p3 → p3)))) ∧ p1) ∨ (p1 → p5)) ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185223331641499508790895812754 : ((False ∧ (((p4 ∨ (p1 ∧ (p5 → p1))) → (p1 → p1)) → p5)) ∨ (((p5 ∨ (p1 ∨ ((p2 ∨ False) → p1))) → (True → False)) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42823643483208227087046260655 : (((p1 → ((((p3 ∨ p2) ∧ True) ∧ p2) → ((False ∧ ((True ∨ p4) → (((True ∧ False) ∨ p3) ∧ p3))) ∧ ((p5 ∧ p2) ∧ p4)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149595882960726122751193927249 : ((p3 ∧ ((((p2 ∨ p3) → ((p4 ∨ p5) → p5)) ∧ (((p1 → p1) ∨ False) ∧ True)) ∧ (p5 ∨ (p1 → True)))) ∨ ((p1 ∧ (p2 → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60394958662610991513252430321 : (((p3 → p4) → (p3 ∨ (p4 ∨ (((p2 → (p2 ∨ (True ∧ p4))) ∧ p1) ∧ ((False ∨ (p4 → p3)) ∧ ((True ∧ p5) ∧ (True ∨ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182476286331895183259731889251 : (((p5 ∨ (p5 ∨ (p2 → (p4 → (p4 ∧ p4))))) ∨ (p4 ∧ False)) ∧ (p3 → ((True ∨ p4) ∧ ((p5 ∧ p3) ∨ ((True → False) ∨ (p1 ∨ True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_317761974729238570033288869291 : (p4 ∨ ((((((True ∧ p4) → True) ∧ p4) ∧ (p4 ∨ ((p4 ∧ (True ∧ False)) ∨ (False → False)))) ∨ ((((p3 ∨ p3) ∧ p5) ∧ p2) → p5)) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718547865134980481829139507645 : (((((p1 → (False ∨ p5)) → False) ∨ ((p3 ∨ ((((p5 ∨ (False ∨ p1)) ∧ (True ∨ (p5 ∧ p1))) ∨ (p5 ∨ p3)) ∧ p2)) ∨ (p1 ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_644487888942926123072409155983 : ((((p1 ∨ ((True ∧ (((p4 ∧ (p1 ∨ True)) → ((((p5 ∨ (p5 ∧ p3)) ∧ p2) ∨ (p2 ∨ True)) → (p1 → p5))) ∨ p2)) ∧ p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66289543742738176698199140975 : ((p5 ∨ ((p2 → p2) ∧ ((p5 ∧ p3) ∧ ((((p5 ∧ (p5 ∨ False)) → p1) ∨ p4) ∧ (((True ∨ p1) ∨ (p2 ∨ p1)) ∧ (p4 → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147092079589757688832815732293 : (((((p5 ∨ p3) ∧ p3) ∧ (False ∧ (True ∨ (((True → True) ∧ (p5 ∨ p2)) ∨ (False ∨ (p2 ∨ True)))))) ∧ p3) ∨ ((p2 ∨ False) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774041671871873481731899307112 : (((False ∨ ((((p2 ∧ (((p2 ∨ p2) ∧ ((((False ∧ p4) ∨ (False → p5)) ∨ p4) ∨ p5)) ∧ (p4 ∧ p4))) ∨ True) ∨ True) ∨ (p3 ∨ p4))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328550455806842780086853191643 : (True → (((((p3 → (p4 ∧ p5)) ∨ p4) → (p2 ∧ (p2 ∨ (p1 ∧ p5)))) ∨ (False → p1)) → ((((False ∨ p5) ∧ p2) ∨ (False → p2)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337591212249952526494076867253 : (p1 → (((p1 → (p4 ∧ p4)) → ((p1 → True) ∧ ((False ∨ p5) → ((p4 → p1) ∧ (p2 ∧ (p2 → True)))))) → ((p4 ∨ p3) ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141789973671797071350819289878 : (((False ∧ p4) ∨ (((p2 → (p3 ∧ (False → True))) ∨ p3) ∨ (((True → p5) ∧ ((p3 → p5) ∨ p1)) → (False → p2)))) → (p3 ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777731415277676052449767589883 : (((p1 ∨ (((p4 ∨ ((False → True) ∧ False)) → p1) ∧ ((((p1 ∧ (True ∨ (p4 → False))) ∧ (p4 ∨ (p2 ∨ p2))) ∨ p4) → (True → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41124941840240401191039060047 : ((((((False ∨ (((p4 ∧ p5) → ((p2 ∧ False) ∨ p4)) → (True ∧ p5))) ∧ ((p2 ∧ p5) ∨ p4)) ∧ True) ∨ (p3 ∨ (p3 → False))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741859926429192388699714986454 : ((((True → p5) ∨ ((True → (((p1 ∨ p4) → p5) ∧ (((p1 → p2) ∧ ((p3 → (p5 → p5)) ∨ False)) ∨ False))) ∨ (p1 ∨ (p2 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65375039970264859398505306148 : ((p3 ∨ (((p4 → ((False → p2) ∧ ((p1 → True) ∨ p2))) ∧ p3) → ((p4 ∧ (((False ∧ (False → p5)) → False) → (True ∧ p2))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722340168348271309458812341830 : (((((p2 ∧ p4) ∧ False) ∧ ((p2 ∧ ((True ∨ True) ∨ (((((p1 → p5) → p5) → (p5 ∨ p2)) ∧ ((False ∨ False) ∨ False)) ∧ False))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147975816397786116626227069427 : ((((((False ∨ (False ∨ (((p5 ∧ True) ∨ p4) ∨ p2))) ∨ (True → (p5 ∧ p1))) ∧ p1) ∧ False) ∨ (p4 ∨ True)) ∨ (False ∨ ((p3 → False) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307314816013837535049617896714 : (p1 ∨ (p3 ∨ ((p5 → ((p2 ∧ p2) → (((p1 ∧ ((((p5 ∧ True) → ((p1 ∨ p2) ∧ True)) ∧ p5) ∨ p2)) ∨ p4) ∨ p5))) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_205628213506776814469833519689 : (((p2 ∧ p2) ∨ (p5 → (p2 → p1))) ∨ ((((False ∨ p4) ∨ (p1 ∨ (True ∧ True))) → ((True ∧ (((p1 → p3) ∧ p2) ∨ True)) ∨ p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
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
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103248270852504975618114130800 : (((p4 ∧ ((True ∧ (p4 → (((((p1 → ((p3 → False) → (True → p1))) → (True ∧ p3)) ∧ p5) ∧ p2) ∧ p1))) → False)) ∨ True) ∧ (p5 → p5)) := by
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
theorem thm_5_vars_346590598995054727768145961126 : (p3 → (((((p4 ∧ (p1 ∨ ((p5 ∧ (p2 ∨ (p3 ∨ (p4 ∨ False)))) ∨ p2))) ∨ (True ∨ p5)) → (p2 → p1)) ∨ p2) ∨ (p5 ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261486799994686234366158197772 : ((p5 → p2) → (p2 → ((p1 → False) → ((((p4 ∨ p4) → False) → (((p2 ∨ p3) ∧ (True ∧ p5)) ∨ p3)) ∨ (((True → p5) ∧ p2) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256562387416158924356478131060 : ((False ∨ p5) → (p3 ∨ ((((p2 ∨ ((p3 → (False ∧ (p1 ∧ p3))) → ((True ∨ p3) → False))) → (p2 ∨ (p1 ∧ (True ∧ p2)))) ∨ p5) ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299084210807726875925094041775 : (False ∨ ((((p1 ∨ ((((((p1 ∨ p5) ∨ (p5 → (p3 ∨ False))) ∧ p1) ∧ (False ∧ p4)) ∧ (p4 ∧ p1)) ∨ (p1 ∨ p4))) ∧ p5) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585371489391915909795547528709 : (((((((p2 ∨ ((p4 → (p5 → p5)) ∧ (p3 → (p5 ∧ True)))) ∧ (True → ((((False ∧ p4) ∨ p1) → p3) → p2))) ∧ p5) ∧ p4) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251597070601154924938622341466 : ((p3 → p1) ∨ (((p5 ∧ ((False ∨ ((p3 → ((False ∧ p3) ∧ ((p1 ∧ (True ∨ True)) ∨ False))) ∨ False)) ∧ (p4 ∧ (p3 → False)))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56093212495419374148204041121 : ((((p3 ∧ p4) ∧ (p3 ∨ p4)) ∨ ((((((((p3 ∧ p2) → True) ∨ (False → p4)) ∧ p4) ∧ ((p1 ∨ p1) ∧ p3)) ∨ True) ∨ p1) ∨ False)) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156878626949648291405208823388 : ((((((((p5 ∨ (((p1 ∨ (p5 ∨ p2)) ∧ p5) → p3)) ∧ p5) ∨ p2) ∨ False) ∧ False) ∨ p2) ∨ False) ∨ (p3 → (False ∨ (p1 → (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50645871435517743672624582236 : (((((p2 ∨ (p4 → p3)) ∧ ((False ∧ (False ∧ p2)) ∨ p2)) ∧ (((p5 ∧ p2) ∨ (p2 ∨ True)) → False)) → ((p3 ∧ p4) ∨ (p3 ∧ False))) ∨ p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : ((p5 ∧ p2) ∨ (p2 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : ((p5 ∧ p2) ∨ (p2 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64390650802897040404572486760 : ((p1 ∨ (((((True ∨ False) ∨ p1) → (False ∨ ((p5 ∧ False) → ((True → (((p4 → p1) → p3) ∧ (p2 ∧ True))) → p3)))) ∨ False) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41645341815625449031541657761 : (((((p5 → ((True ∧ True) ∧ p3)) ∨ True) ∧ ((False ∨ p3) → ((True ∧ (((p4 ∨ False) ∧ (False ∨ (p2 ∧ False))) ∨ p2)) ∨ False))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254635613738439217139379842334 : ((p3 ∧ p2) → (((p1 ∨ ((((p2 ∨ p2) ∧ p5) ∧ p1) ∨ p3)) → (((p4 ∨ (p4 ∧ p5)) ∨ (False → (p4 ∨ (p2 ∨ p4)))) ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64043796421647131191168894620 : ((False ∨ ((p5 ∨ ((p1 ∨ ((False ∨ (((False ∨ (p2 → p5)) ∨ p3) → (p4 → p2))) → (False ∧ True))) ∨ True)) ∨ ((p4 ∧ True) → p3))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746286988553278118415504231182 : ((((p1 ∨ p5) → (p2 ∨ (((p3 ∨ (((True → p4) ∨ p4) ∨ p4)) ∨ ((p2 → p1) → (p1 ∧ p4))) ∧ (((p3 → False) → p4) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355687253658770824959259837530 : (p5 → ((((p3 ∨ (p3 ∧ ((True ∨ p5) → (p4 → (p5 → p1))))) ∧ (True ∨ ((p4 ∧ p2) ∨ True))) ∧ ((p5 ∧ p3) → p2)) → (p2 ∨ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : (p5 ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h1
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : (p5 ∧ p3) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h21 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h22 : (p5 ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h1
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h23 := h4 h22
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h29 : (p5 ∧ p3) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h30 := h4 h29
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140335517779337306677946762095 : (((((p3 ∧ ((p5 → (p4 → (p5 ∧ p4))) ∨ (p4 → p1))) ∧ (p2 ∨ (p2 ∨ p2))) ∨ False) ∨ (False ∧ (False → p4))) → ((p4 ∨ p2) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237875341719122448533789465176 : ((True ∨ True) ∧ ((False ∧ ((((p4 ∨ ((((p4 ∨ True) ∧ (True ∧ p4)) ∧ (p5 ∧ p4)) ∧ p1)) ∧ p5) ∧ (p3 → (p1 ∧ p2))) ∧ p3)) ∨ True)) := by
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
theorem thm_5_vars_354628154776811196222493199270 : (p5 → (((p4 ∧ ((p4 → ((p5 ∨ (p1 → (((p4 ∧ p5) ∧ ((p2 ∧ ((p1 ∨ p4) → p3)) ∨ p3)) ∨ p1))) ∧ p1)) → p1)) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149241409990348487371005625137 : (((False ∨ False) ∨ (p4 → ((False ∨ (p4 ∨ p5)) ∧ (((((p3 → True) → p1) ∧ False) ∨ (p4 → False)) ∨ p1)))) ∨ ((p4 ∧ (p4 → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60381621801976256870020596674 : (((p3 → p2) → (((((p1 ∨ p3) ∧ (p5 ∧ p5)) ∧ p5) ∨ (True → p1)) → (p1 ∨ (((p3 ∧ p5) → True) → ((p4 ∨ p3) ∧ p2))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h7.left
      let h13 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h15
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2280904183799606826681438188 : (((p2 → (p2 ∧ ((p3 ∨ (p1 → p2)) ∨ (p1 ∨ p5)))) → (True ∧ False)) ∨ ((p3 ∨ p5) → (True ∨ (((True ∧ False) ∨ False) → p4)))) := by
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
theorem thm_5_vars_215117037767756402297943338212 : (((p2 → p5) → (p5 ∨ p2)) ∨ (((((True → p5) → p4) ∧ (p1 ∨ (p2 → ((p3 ∨ (p4 ∨ (p5 ∨ True))) ∨ True)))) ∨ p3) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184295108863782665524105320312 : (((((p1 ∨ p4) → True) ∧ (p4 → ((False ∨ p3) ∧ False))) → p3) ∨ (False ∨ (p1 ∨ ((p3 → (p1 ∨ (((False → p2) → False) ∨ False))) ∨ True)))) := by
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
theorem thm_5_vars_138257639835182105664885653922 : ((p2 → (p4 ∧ (p4 ∧ (p1 ∨ ((p4 ∧ (p5 ∨ p2)) ∨ ((p3 ∧ (p2 ∨ p2)) ∧ (True ∧ ((False ∨ p3) ∧ p4)))))))) ∨ ((p1 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597741667667619878447025898756 : (((((False ∨ (p3 ∧ (p2 ∧ p2))) → (p4 ∨ (((p4 ∧ (((True ∨ True) → (p5 ∨ p3)) ∧ (p5 ∨ (True → p5)))) ∨ False) ∨ p2))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53916865809937574737171246705 : (((p1 ∨ (((p5 ∧ False) ∨ (p2 ∧ True)) ∨ (False ∨ True))) ∨ (((p5 ∨ ((p1 → (False ∨ True)) ∨ ((p4 → p5) → True))) ∨ True) ∨ p3)) ∨ False) := by
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
theorem thm_5_vars_247987475411779031249743601053 : ((p1 ∨ p4) ∨ ((True ∧ p3) ∨ (((p5 ∧ ((((((True ∧ p3) → p4) → (False ∨ (p5 → (p3 ∨ p5)))) → p2) → p3) → p4)) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81060264993900166431617121193 : (((((p1 ∨ (True ∨ p1)) → (False ∧ p3)) ∧ (p5 ∨ (False ∨ (True → (p4 → ((p5 ∨ p4) ∨ (True ∨ True))))))) ∧ ((p1 → False) → True)) → False) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ (True ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : (p1 ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178091706708544549754710049682 : ((((p2 ∧ (True → (p1 ∨ ((p5 ∧ p3) → (p2 ∨ p1))))) → False) → p2) ∨ (p4 ∨ ((p5 → p4) ∨ (((True → p5) ∨ True) ∨ (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_45808605485825373349067679175 : (((p1 → (True ∨ ((p3 → (p5 ∧ (p3 ∨ (p2 ∨ ((p2 ∨ p4) ∧ (((p2 ∧ False) ∨ p1) ∨ p1)))))) → (True ∧ (p3 → p1))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245657791295585438371675761683 : ((p3 ∧ p1) ∨ ((((p1 ∧ (True → ((((p5 ∨ p4) ∨ p3) ∧ p4) ∧ (p1 → (False ∧ p1))))) ∨ (p3 ∨ (p3 ∧ p4))) → p3) ∨ (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784463493933753019115506556794 : (((p3 ∨ (p5 ∧ (((((p5 ∧ p4) ∧ p3) → True) ∧ p5) ∨ (p5 ∧ (False ∧ (False ∨ (((p3 ∨ ((p1 ∨ p1) ∧ True)) ∧ False) → p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684085751120887759080129629734 : (((((((p2 → (((p5 ∨ (p1 ∧ p4)) ∨ (p5 → p1)) → p2)) ∨ p5) ∧ p1) ∧ (p3 → True)) ∨ ((p4 ∨ False) ∨ ((p5 → p2) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37225658445225673477133046702 : (((((p1 ∨ True) ∧ (p1 ∨ ((((True → ((((p5 → p5) ∧ ((False ∨ p2) → p2)) ∧ p3) → p2)) ∧ p1) ∨ False) ∧ True))) ∧ True) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148071231828076149242409228868 : ((((((False → False) ∨ (((p2 ∨ (((p2 ∧ p5) ∨ p4) ∧ True)) ∧ False) ∨ False)) → p1) ∧ p1) → (p3 ∧ p5)) ∨ (((p5 ∨ p1) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50048887766052029317595598914 : ((((False ∧ p2) ∧ (p3 ∨ ((p5 → (p5 ∧ (((p3 ∧ p4) ∧ p5) → (p1 ∨ p5)))) → (p5 ∧ p1)))) ∧ (((p4 ∨ False) ∨ p4) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158168575479451772743875624138 : (((((p4 ∧ p3) ∧ p2) → p4) → (p5 → (((p3 → (False ∨ (p1 ∧ (p2 ∧ True)))) → True) ∧ p3))) ∨ ((((False ∧ False) → p2) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112618536434965379089311325299 : ((((p1 ∧ (((False ∨ p3) ∧ (p5 ∧ (p1 ∧ (((False ∧ p2) ∧ ((True → p4) → p1)) → p3)))) → p4)) ∨ (True ∨ p4)) → False) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61961905115967134773775127526 : ((p2 ∧ (((((p4 → (True → (True ∧ (p3 ∧ True)))) ∨ p2) ∨ p2) ∧ False) ∨ ((p3 ∧ ((p1 ∨ (True ∨ p1)) → (True → p3))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300957235837778417309771425075 : (False ∨ ((((p1 ∨ (True ∧ (p3 ∧ p4))) ∧ ((True ∧ True) ∨ p3)) ∨ False) ∨ ((p4 → p4) ∧ (p4 ∨ (False ∨ (p4 → (p5 ∨ (True ∨ p1)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304985200716360589726557015882 : (p1 ∨ ((((p4 ∨ p3) ∨ ((p3 ∨ True) ∧ ((((False → p4) ∨ p2) ∧ (True ∧ p5)) → ((p3 ∧ True) ∨ p4)))) ∨ True) ∨ (p1 ∧ (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321329392758368744934635816190 : (p4 ∨ (p5 ∨ (True ∧ (((p2 ∧ p3) → ((p1 ∧ p1) ∧ (((True → p5) → ((p4 ∨ p2) → p5)) → (p5 ∧ ((True ∧ True) → p4))))) ∨ True)))) := by
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



