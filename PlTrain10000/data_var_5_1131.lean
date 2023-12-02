variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254149437090286453915549973649 : ((p2 ∧ p1) → (((((((p3 ∧ True) → p5) ∨ p3) ∨ (p3 ∧ (p3 ∧ p3))) → False) ∨ (((p3 ∧ ((p1 ∨ p5) ∧ p1)) → False) ∨ p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191418211467661734218759187052 : (((True ∨ p3) → (p1 ∧ (((p4 ∧ p1) ∨ False) ∧ p3))) ∨ (p1 → (p5 → (((p1 ∧ (p2 → p1)) ∨ ((p5 ∧ p2) ∨ p5)) ∨ (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180878157890489745748849910718 : ((((p3 ∧ p3) ∧ p5) → (True → (p3 ∨ (p2 → (True ∧ (True → p4)))))) → ((((p5 → False) → (p2 ∨ (p2 ∧ (p2 ∧ p3)))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695761209251372744326716238537 : (((((False → (p5 ∧ p3)) ∧ (((p1 ∨ True) → ((p1 → p2) ∨ p2)) ∧ p1)) → ((p1 → p3) ∧ ((p3 ∨ p1) ∧ (p2 ∨ (True ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164974869155047067470267680465 : ((((p2 → (p5 ∨ ((p3 → (p1 → ((p3 ∨ False) ∨ p3))) ∨ p4))) ∨ (p2 → p5)) → p3) ∨ (p3 ∨ ((p4 ∧ ((p1 → p3) ∧ p5)) → p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227210735323544379783430380684 : (((True → p5) → p1) ∨ ((((p1 ∨ True) → p3) ∨ p3) → (((p2 ∧ p2) ∨ p4) ∨ ((p2 ∧ True) ∨ ((p3 ∨ (p1 ∧ p5)) ∨ (p4 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304714565858194083025875388556 : (p1 ∨ (((p5 ∨ (p5 ∧ (p1 ∧ (((p4 ∨ (False ∨ p4)) ∨ (p1 ∨ ((False ∧ p4) ∧ (p4 ∨ p3)))) ∨ False)))) → (p4 ∨ p4)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228915121232130345173730389636 : ((p4 ∨ (False ∨ p2)) ∨ (((((True → ((p5 ∧ ((p3 ∨ p3) ∨ p1)) → p5)) → (p1 ∧ True)) ∨ ((p4 ∧ True) ∨ p1)) ∨ p4) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113017288783386640863680951224 : (((p5 ∧ ((False ∨ (True → p1)) → ((True ∧ True) ∨ ((p5 ∨ ((p3 ∧ (p1 ∨ (p3 → p4))) ∧ p4)) ∧ (p1 ∧ p4))))) → False) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694389655672072382632897730814 : (((((p2 → False) ∧ (p4 ∧ (((((p2 ∨ p2) → p1) ∧ p4) → False) ∧ True))) ∨ (True ∨ (((p4 → ((True ∧ p4) ∨ p2)) ∨ p1) ∨ p2))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_328568425231687112241407635193 : (True → ((p5 ∨ ((((p5 ∨ p4) → (p4 → ((p3 ∨ p4) → True))) → p4) ∧ (p2 → p5))) → ((((False ∨ True) → p2) ∧ p4) ∨ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251328796799290790167765429047 : ((p2 → p3) ∨ ((p1 → p2) ∨ ((((((((p1 ∧ p1) ∨ p4) ∨ ((p5 ∧ p4) ∨ True)) ∨ (p2 → (p2 ∧ p5))) → p2) → p2) ∧ True) ∨ p4))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ p1) ∨ p4) ∨ ((p5 ∧ p4) ∨ True)) ∨ (p2 → (p2 ∧ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43177371454853591798052831691 : (((((p1 ∨ p3) ∧ (p3 → ((p3 ∧ ((True ∧ (p3 ∧ p5)) ∧ (p3 → (p4 ∨ (p3 ∨ ((True → p5) → p5)))))) ∨ p1))) ∧ p2) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637458020107614986119598100265 : ((((((p1 ∨ p2) → ((((p4 ∨ p3) ∧ p3) ∧ False) ∨ p2)) ∧ ((True ∧ False) ∨ (((p3 ∨ p2) → p1) → ((p1 ∨ p5) ∨ p2)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171755673773237292640392473876 : ((((((p2 ∧ False) ∨ ((False ∧ (True ∧ p2)) → (p3 → True))) ∧ p1) → p4) → p5) ∨ ((True → (p1 ∧ (False ∧ (p1 ∨ p5)))) → (False ∨ p4))) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658554271998226499568353773141 : ((((p2 ∨ ((False → True) → (((p3 ∨ (p4 ∧ ((p1 ∨ p2) → (p2 ∨ p5)))) → ((p4 ∨ False) ∨ (p4 ∧ p1))) ∧ p4))) ∨ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252651160829918208990759812979 : ((p5 → p4) ∨ (((p4 ∨ ((p2 → False) ∨ (p5 ∨ (((p3 ∧ p3) ∧ True) ∨ False)))) ∨ p5) ∨ (((False ∨ (False → p4)) ∧ True) → (True → True)))) := by
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
theorem thm_5_vars_233240415074753486645296925142 : ((True ∨ (True ∧ p3)) → ((p2 ∧ p4) → (((False ∧ p5) ∧ (p4 ∨ (p4 ∨ (p2 ∧ p4)))) ∨ ((p1 → p5) → (p5 ∨ (True ∧ (p2 → p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43097133710667258735045065183 : ((((((p3 ∨ (p2 → (((p5 → (True → p4)) ∧ (p2 ∨ p2)) ∨ (False ∧ (p1 ∨ True))))) ∨ p2) ∧ ((True ∨ p4) → p2)) ∧ True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172539075136200960912570208154 : ((((p2 ∧ p4) ∧ p3) ∨ (((((p5 → True) ∨ (p1 ∨ p1)) ∧ p2) ∧ p5) ∨ True)) ∨ (p4 ∨ (p4 ∨ ((True ∨ p2) ∧ (p3 ∨ (p4 ∨ False)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67704140492878434237528127215 : ((p1 → (p5 → ((((True ∨ (True ∨ False)) → p1) → (False ∨ False)) ∨ (((p1 → (True ∨ p5)) ∧ (p2 ∧ (p3 ∧ False))) ∨ (p2 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1947529310354013268295317322 : (((((p2 ∨ (True → p4)) → False) ∧ (((((p3 ∨ p3) → (p2 → True)) ∨ p1) ∨ p3) → p4)) → p2) ∨ (p5 ∨ (p1 → (True → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ (True → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((((p3 ∨ p3) → (p2 → True)) ∨ p1) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60470381723398452663516706558 : (((p5 → p4) → (((((p2 ∨ p2) ∨ p4) → (((p5 ∨ p1) ∧ p3) → (p2 ∨ p4))) ∨ (p2 → ((p5 → p2) ∧ p3))) ∧ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113555400401168001500281931608 : ((((p2 ∧ False) ∧ ((False ∨ p3) ∨ ((True ∨ p1) ∧ (((p4 → ((False → p5) ∨ p3)) ∧ (p4 ∧ True)) ∧ p1)))) ∨ (p4 ∧ p5)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709234482005031019770238732072 : (((((p2 ∧ True) ∨ (((p4 → p2) ∨ p3) → p5)) → (((p1 ∨ False) → (((True → (True ∧ p1)) ∧ False) ∧ p5)) ∧ ((p4 ∧ p5) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336320656469148637980275292314 : (p1 → (((p4 → (p2 ∨ (p3 ∨ True))) → (((((True ∧ p3) ∧ p1) ∧ ((p2 → p4) → ((False ∧ False) ∧ True))) → p1) → (p4 → False))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326026786112386426238574253904 : (p5 ∨ (True → (p2 → (((p2 ∧ ((((((p5 ∨ p3) → (p3 ∧ p1)) ∨ p2) → (False ∧ (p4 → (True → True)))) ∧ False) ∨ p2)) ∨ p2) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115882239497791512151286336679 : (((((False ∧ p2) ∧ p1) ∨ p2) ∨ ((False ∨ ((True ∨ ((((p3 ∨ p1) ∧ p1) → (p2 → False)) ∨ True)) ∨ (p2 ∧ p3))) ∧ True)) ∨ (p3 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_55367889172746970056058613162 : (((p5 → (p3 ∨ ((p1 ∧ p2) ∧ p3))) ∨ ((p3 → ((p2 → (True → False)) ∨ (p5 ∧ ((False → (False ∧ p3)) → True)))) ∨ (p3 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1492237495344697969755641277 : (((((p2 ∨ ((True ∨ p1) → (False → p2))) → (((False ∧ p2) ∨ (False → True)) ∧ False)) → (p2 ∨ p5)) ∨ (p4 ∧ p3)) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((True ∨ p1) → (False → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677429468765380777683226456943 : (((((((p2 ∨ p5) ∧ (((p4 ∨ p2) ∨ ((p1 ∧ (True ∧ p4)) ∧ p2)) ∨ True)) ∧ (p5 ∨ p4)) ∨ p4) ∨ (p4 ∧ ((True ∨ p4) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117783351821847764739475852076 : ((p4 ∧ ((((p5 ∨ p2) ∨ ((p2 ∨ (p2 → p4)) ∨ p3)) ∧ (p1 ∧ ((p4 ∧ p3) → p5))) ∨ ((False → p4) ∧ (p4 ∨ p2)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119827983644047166555383467559 : (((((True → p4) ∧ (((((p5 ∧ p4) ∨ (True ∧ ((False ∧ True) ∧ False))) ∧ p5) ∧ ((True → p2) → p1)) → p1)) → p5) ∧ p2) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741384812205165224225189592427 : ((((p5 ∨ False) ∨ (((((True ∧ ((True ∨ p2) ∧ True)) → p2) ∧ (p5 → (p3 ∨ p4))) ∧ (((p2 ∨ p1) ∨ True) → False)) ∨ (True ∨ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52757207148935018241848654123 : (((((True ∧ (p4 ∨ ((True ∨ (False ∨ False)) ∨ (p2 → p2)))) → p2) → p3) → ((((True ∧ False) ∨ p3) → (False ∧ p5)) ∨ (False → p2))) ∨ False) := by
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
theorem thm_5_vars_213469017274670406961491127499 : (((False → (False ∨ p4)) ∧ p2) ∨ (((p3 → p2) → p2) ∨ (p3 → (False ∨ (((False → False) ∧ (p2 → p3)) → (True → (p2 → (p4 ∨ p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112175759752763586603701975480 : (((p4 ∧ ((p1 → (False → ((p5 ∨ (((p4 → (False ∧ p2)) ∨ (True → ((p1 → p3) ∨ p4))) ∧ p1)) ∨ p2))) → p4)) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41305929566075036037973306367 : (((((p5 ∧ ((p4 ∧ (((False ∨ ((p1 → p5) → False)) → False) → p4)) ∧ p2)) ∧ p1) ∧ (p3 ∨ (p3 ∨ (p3 ∨ (p2 ∨ False))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183873615090925850494874066507 : (((((p2 → p2) ∧ p2) ∧ (p1 → ((True ∧ p5) ∧ p3))) ∧ False) ∨ ((p3 → (((((True → p5) ∧ p5) ∨ p2) ∨ (True ∧ p5)) ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53212518248975585795032300080 : ((((((p2 → p5) ∨ (p1 ∨ p1)) ∨ p4) ∨ ((p3 ∨ p3) ∧ p3)) ∨ ((((p1 ∧ True) → p3) ∧ p2) → (((p3 ∧ p5) → p5) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648583250506367252739626907160 : ((((((((p2 ∨ (p1 ∨ p5)) → p2) ∨ (True → (p3 ∨ False))) → (p1 → ((p5 → (p1 → (p1 ∧ p5))) → False))) ∨ p4) ∧ (p4 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266036829288287912881237791574 : (True ∧ (p1 → (p1 ∧ ((((False → ((p1 → (True ∧ False)) → (p5 ∧ p3))) → ((p2 ∨ True) → p3)) ∨ p4) ∨ (True ∨ (True ∨ (p2 → False))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310512974288715521990584279804 : (p2 ∨ ((p2 ∨ ((p3 ∨ p5) ∨ (p5 ∧ p5))) ∨ (False → ((False ∨ ((p3 ∨ ((True → p3) → (p4 → True))) ∧ (p2 → (p4 ∧ True)))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254454193907001030145061914349 : ((p3 ∧ True) → (((p2 ∧ False) ∨ (((((False ∧ True) ∧ (p1 ∧ False)) ∨ p4) ∧ (p5 → ((False → p5) ∧ (True ∧ p4)))) ∨ (p4 ∧ p1))) ∨ True)) := by
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
theorem thm_5_vars_756500827020583594753184864336 : (((p1 ∧ (((p3 → ((p2 → (p2 → (p1 → (p5 ∨ (p1 → p5))))) ∧ ((p4 ∧ False) ∨ False))) ∨ p2) ∨ (p4 ∨ (p1 → (p3 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166239227640497190828286227627 : ((p2 ∧ (p3 ∨ ((False ∨ p1) ∧ ((True → ((True → p1) ∧ True)) ∨ (p5 → (False ∨ False)))))) ∨ (True → (p5 ∨ (p1 → ((False ∧ p4) → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203972083367612172085194267823 : ((p3 → ((p1 ∨ (True ∧ p5)) ∨ p3)) ∧ ((p3 ∨ ((p3 ∨ True) → ((p1 ∨ ((p3 ∨ p5) → p2)) ∧ (p3 ∧ ((p4 ∧ p1) → p3))))) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114007255799328261980804835015 : ((((((False → p4) ∧ ((True → p3) ∨ p2)) ∨ ((p3 ∨ (p5 ∧ p1)) → ((p1 ∧ p2) ∨ p1))) ∧ p1) ∨ (p5 → (True → True))) ∨ (p1 → p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52289256509744283526650322036 : (((p5 → (p4 → ((p1 ∨ (p1 ∧ (p4 ∨ (p4 → (p3 ∨ (True ∧ p2)))))) ∧ True))) → (True → (p2 → (p3 ∨ (p1 ∧ (p1 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253739519885033496070572791770 : ((p1 ∧ p1) → ((((p2 ∧ (((((p4 ∧ False) ∧ p4) ∨ (((p4 → p3) ∧ p3) ∨ p4)) ∨ p1) ∧ p2)) → p5) ∨ p3) → ((p3 ∨ True) ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254063988716385092449215557704 : ((p2 ∧ True) → (True ∧ ((((p5 ∨ True) ∨ (p3 → p5)) → False) ∨ (p2 ∨ (((p5 ∧ (p2 → (p4 → ((p3 ∧ p4) → p3)))) ∨ False) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53516305734152667517172510274 : (((False → ((p4 ∧ (((p2 ∨ p3) ∧ (True → False)) → p3)) ∨ p5)) → ((p3 → ((True ∧ (p4 ∧ (p4 ∨ p4))) → (p4 ∨ p2))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773655892379483348099169707325 : (((False ∨ ((True → (((False → p3) ∧ (((((p5 ∨ (p1 ∨ (p3 ∨ False))) ∧ (True ∨ p2)) ∨ p2) ∧ p4) ∨ p2)) ∧ (p4 ∨ True))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167049762682832414039352641790 : (((((((((p1 ∧ p4) ∨ p5) ∧ (p4 ∨ p5)) ∧ (p1 ∧ p3)) → p5) → p4) ∨ p4) ∨ True) → ((p3 ∨ (p2 ∧ (p3 ∨ (True → p2)))) ∨ True)) := by
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
theorem thm_5_vars_315468826257077379644845887310 : (p3 ∨ (((p2 ∨ True) ∨ p5) → ((p3 ∧ ((p2 → True) → (p5 → (p5 ∨ (p4 ∨ (p4 → (p2 ∧ p4))))))) ∨ (((p4 ∧ p5) ∧ p3) ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49038501856094216810970647843 : ((((True ∨ ((p4 → (p4 ∨ ((p5 ∧ (p4 ∧ p5)) → (False → ((p2 ∧ p4) ∨ (False ∨ p4)))))) ∨ p4)) → p3) ∨ ((p4 ∧ False) → p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_248338236841726327318130952531 : ((p2 ∨ p3) ∨ ((p4 ∨ ((((p2 ∧ p5) → False) ∧ p4) ∨ ((p3 ∧ p1) ∧ (p2 → (p3 ∧ p5))))) ∨ (p1 → (p1 ∧ ((p3 ∨ False) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38564877994585086169366867491 : (((((((p4 → p4) → True) ∨ p4) → (p2 ∧ (False → p5))) ∨ (False ∧ (p3 ∧ ((p3 ∨ ((p1 → p3) ∧ (True → p4))) ∧ p1)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719270705792174604488634392339 : ((((p4 ∧ ((p3 → p2) ∨ p4)) ∨ ((((False ∧ ((p1 ∧ ((p3 ∧ (p1 → True)) → True)) ∨ (p5 ∧ p1))) ∨ True) ∨ p2) ∨ (True ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148940235189759892182197622253 : (((p1 ∨ (True ∨ (p2 ∧ True))) → ((p2 ∧ ((False ∧ (((p3 ∨ False) → p1) ∨ (p1 ∨ p3))) ∧ p3)) ∧ p4)) ∨ ((p5 → True) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230642738466014836965669242273 : (((p3 → True) ∧ p3) → (p2 → ((((False → False) ∨ (False → (True ∨ (True → (p1 → p2))))) → False) ∨ (p2 → ((True ∨ True) ∧ (p3 → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135331923232810348191040182042 : ((((p4 ∨ (p1 ∨ (p3 ∧ True))) ∧ ((p1 → p1) → ((True ∨ ((p3 ∧ p4) → p4)) ∧ p5))) ∧ ((False ∨ p4) ∧ p3)) ∨ ((p4 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69174490531372741603351708035 : ((p5 → ((((p5 ∧ (p5 → True)) → False) ∨ (((p5 ∧ (True ∨ (p4 ∧ False))) ∨ p4) → False)) → ((False ∧ ((p1 ∧ p2) ∨ False)) ∨ p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 ∧ (p5 → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p5 ∧ (True ∨ (p4 ∧ False))) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41726355598330551724952667841 : (((((False ∨ (p4 ∨ True)) → p5) ∧ (False ∧ ((p4 → (p2 ∨ (p2 ∧ (True → p3)))) ∧ ((p2 ∧ ((p2 → False) ∧ True)) ∨ p1)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721522251169636671842139399389 : ((((p3 ∧ ((True → p1) → p4)) → (((((True ∨ (p4 ∧ (p5 → (p5 ∨ False)))) ∧ (p1 ∨ (p4 → (p1 → p2)))) ∧ p1) ∧ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153159782089952425049715488630 : ((p5 ∧ (((((p2 ∧ p4) → ((True ∨ p2) ∨ (p5 ∨ (p5 → p2)))) ∧ p4) ∧ (True ∧ p2)) → (p4 ∧ p3))) → (((p1 ∨ False) → p2) ∨ True)) := by
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
theorem thm_5_vars_341071804958927468829364994649 : (p2 → ((p5 ∨ (((p5 → p5) ∧ (p2 ∨ (p5 → p5))) → (((p4 → (False → (((p1 ∧ p1) → p4) → p1))) ∧ (p2 → p1)) ∨ True))) ∨ False)) := by
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
theorem thm_5_vars_612542617151670258865166425623 : ((((((p5 → (((p1 ∨ p4) ∨ (((((p1 ∧ p4) ∨ (True ∨ p4)) ∨ (True ∧ p5)) ∧ p4) ∧ p2)) ∨ p5)) ∨ True) ∨ (p2 → True)) ∨ p3) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117154384588879274423055905645 : ((True ∧ ((((((False ∨ ((False → p4) ∨ (True ∧ p3))) ∧ p4) → (p2 ∨ (((p4 → True) → p2) ∨ True))) ∧ p4) ∧ p4) ∨ True)) ∨ (p1 ∧ p1)) := by
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
theorem thm_5_vars_40661036319371058938678343653 : ((((((True ∨ ((p1 ∧ (p2 → p1)) → p4)) ∨ ((p4 ∧ (((True ∨ (p3 ∧ False)) ∨ p5) → p2)) → p1)) ∨ (p5 → p4)) → p4) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149233723490259589269020094846 : (((p5 ∧ p2) ∨ (p4 ∨ (p4 ∨ (p4 ∨ (p1 → (p2 ∨ (True → (True ∨ (p4 ∨ ((True → p5) → p1)))))))))) ∨ (p5 ∨ (p5 → (p5 ∧ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134874523336804338360483539144 : (((p2 → ((((True ∨ (p5 ∧ (False ∨ False))) ∨ (p2 → (p5 ∨ (p1 → (p4 ∨ True))))) ∨ (p3 ∧ p1)) ∨ p5)) → p4) ∨ (True ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678336518719336424316312852853 : ((((((p4 → p1) ∧ ((p2 → p4) ∨ p4)) ∧ ((p2 ∨ p5) ∨ (p3 ∧ ((p2 → False) → (p2 ∧ True))))) ∨ ((p3 ∧ (p2 → p2)) → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_635390225589936643441502999538 : (((((((p5 ∨ (p5 → p2)) ∧ p2) → ((((True ∨ p4) ∨ (p5 ∧ (p1 ∨ p5))) → p5) → p2)) ∧ ((p1 → (p4 ∧ p5)) → p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684742581177625511366538679687 : (((((p2 → False) ∧ ((False ∧ p2) ∨ ((((False ∨ ((p1 ∧ p2) ∧ p1)) ∧ p5) ∨ False) ∧ p1))) ∨ ((p4 ∧ p3) ∧ ((p5 → False) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765822249882358030780500383770 : (((p4 ∧ (((p1 ∨ (p1 ∨ (p5 → p1))) ∧ True) ∧ (p3 ∧ (((p1 → ((p5 ∧ (False → p5)) → p1)) → (p1 ∧ (False ∧ p5))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59296292477098578799889362982 : (((p3 ∨ p5) ∨ ((p1 ∨ ((p1 ∨ (((False ∨ p4) ∨ False) ∨ False)) → True)) ∧ (True ∧ (False ∨ ((((p2 ∧ True) → p1) ∨ True) ∨ p2))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342155500223182670963972044637 : (p2 → (((((((p1 → p4) → p3) ∨ ((p5 ∨ p2) ∧ (p2 ∨ p5))) → p4) → p3) ∧ (p3 ∨ (p4 ∨ False))) ∨ ((True ∨ (p2 ∧ False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214014866754387449433865096250 : ((((p4 ∧ p4) ∧ p4) → p5) ∨ (((p3 ∨ p5) ∧ p3) ∨ ((p2 ∧ (p4 ∨ (p2 → (((False ∧ (False ∨ p1)) ∧ (p5 ∨ False)) ∧ p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300545445677467332109910226339 : (False ∨ ((((p1 → ((p2 → (p5 ∧ (((p3 ∨ p4) ∧ p4) ∧ False))) ∨ (True ∧ p3))) ∧ p2) ∨ (p3 ∨ p1)) ∨ ((False → p2) ∨ (p4 ∧ p2)))) := by
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
theorem thm_5_vars_65947355423422576105015551297 : ((p4 ∨ (p2 ∨ ((True ∧ (((p1 ∧ (False ∧ p2)) ∧ (True → False)) ∨ p5)) ∨ (p5 ∨ (((p1 ∨ True) ∨ (False ∧ False)) → (p3 → p3)))))) ∨ p3) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44161292654759215721194534699 : (((((p5 ∧ ((p4 ∧ (True → (p2 → (True ∧ p4)))) ∨ (True → False))) ∧ (((p5 → p4) ∧ p5) → p2)) → (p2 → (p3 ∧ False))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53285831926182621688251552868 : (((p5 ∧ ((p4 ∧ p4) ∨ ((True → ((p4 → p1) → p4)) ∨ p2))) ∨ (False → (p2 ∨ (((p3 ∨ (p3 ∨ False)) → (p2 ∧ False)) → p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678858772105269129389029563885 : ((((p1 ∧ ((((p5 ∧ p3) ∨ p2) → p1) ∧ (p5 ∧ ((((p1 → (False ∧ p1)) ∨ False) → p5) → p1)))) ∨ (p3 → (False → (False → p3)))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305781576064545328304808224706 : (p1 ∨ ((p4 ∧ (p3 ∨ ((p4 → p5) → (p4 ∧ p3)))) ∨ (p4 → ((((p4 ∨ p2) ∧ p5) ∨ p2) → ((p3 → p3) ∨ (True → (p4 ∨ p4))))))) := by
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
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121122635411219795195122009408 : (((True ∨ ((((p4 ∨ True) ∨ p5) ∨ (p3 ∧ (((p4 → (p5 ∧ (p1 ∧ (p2 → p2)))) ∧ True) ∧ (False ∨ p1)))) ∧ p2)) ∨ p1) → (p4 ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h9
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
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300265514428668933864070423467 : (False ∨ ((False ∨ (((False ∨ p3) ∨ (((False ∧ False) ∧ p5) ∨ (True ∨ (p3 ∧ (False ∨ (p5 → (p3 ∧ (p1 → p1)))))))) → p2)) → (p3 ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((False ∨ p3) ∨ (((False ∧ False) ∧ p5) ∨ (True ∨ (p3 ∧ (False ∨ (p5 → (p3 ∧ (p1 → p1)))))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197708038956234351330932692250 : (((p4 → (p5 ∨ (True ∧ p2))) → (p4 ∨ p2)) ∨ (p4 → (((((p4 ∧ (p2 ∧ False)) ∧ p1) → p5) ∨ (p2 → True)) ∧ (p3 → (p2 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203000686385718720704249218971 : (((False ∧ p4) → ((True → p5) → p1)) ∧ (True → ((((p1 ∨ True) ∧ ((p5 ∨ p4) → False)) ∧ (p5 ∧ (p4 → (p3 → p4)))) → (True → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h9.left
    let h14 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h9.left
    let h17 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937907289564857906052941632387 : ((((p2 ∨ ((p4 ∨ (True ∧ p5)) ∨ p3)) ∧ ((((p1 ∧ True) → (p3 → ((True → p3) ∧ p5))) → ((p1 ∧ (p1 ∨ p3)) ∧ p3)) ∧ p5)) → p3) ∧ True) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p1 ∧ True) → (p3 → ((True → p3) ∧ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h8.left
      let h12 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h7
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h3.left
        let h21 := h3.right
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h22 : ((p1 ∧ True) → (p3 → ((True → p3) ∧ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h25
          -- Conjunctions on the left can always be decomposed.
          let h26 := h23.left
          let h27 := h23.right
          -- One of the premise coincides with the conclusion.
          exact h24
          -- Conjunctions on the left can always be decomposed.
          let h28 := h23.left
          let h29 := h23.right
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h30 := h20 h22
        -- We need to get the right conjuct of h30 based on <expert-advice>.
        let h31 := h30.right
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h3.left
        let h36 := h3.right
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h37 : ((p1 ∧ True) → (p3 → ((True → p3) ∧ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h38
          -- Implications on the right can always be decomposed.
          intro h39
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h40
          -- Conjunctions on the left can always be decomposed.
          let h41 := h38.left
          let h42 := h38.right
          -- One of the premise coincides with the conclusion.
          exact h39
          -- Conjunctions on the left can always be decomposed.
          let h43 := h38.left
          let h44 := h38.right
          -- One of the premise coincides with the conclusion.
          exact h36
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h45 := h35 h37
        -- We need to get the right conjuct of h45 based on <expert-advice>.
        let h46 := h45.right
        -- One of the premise coincides with the conclusion.
        exact h46
    case inr h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h3.left
      let h49 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h47
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391618102966225170325552556819 : (((((p3 ∨ ((p4 ∧ p1) → True)) ∧ ((p1 ∨ ((p2 → (p4 ∧ p5)) ∧ (p2 ∧ (p1 ∨ ((True → (True ∨ False)) → p5))))) ∨ p1)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_246153351008396847870891386424 : ((p4 ∧ p2) ∨ ((p4 ∧ (((p3 ∨ p2) ∨ ((False → p1) ∨ (p3 ∨ (p4 ∧ True)))) ∨ p1)) ∨ ((p1 ∧ p4) ∨ (True ∨ (p2 ∨ (p5 ∨ p3)))))) := by
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
theorem thm_5_vars_171122936962547539671786162110 : ((False → ((False ∨ ((p3 → (p5 ∨ p3)) ∧ (p4 ∧ (p3 ∨ p3)))) ∨ (p5 ∨ p3))) ∧ (((p5 ∨ p1) ∧ (p2 ∧ p5)) ∨ (p3 ∨ (p3 → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57625780234340222586176976404 : ((((p2 ∧ True) ∨ p3) → (((p5 ∨ p5) ∧ (p2 ∨ ((((p5 ∨ p5) ∧ False) → (p5 → (p5 → ((p5 ∨ True) → p4)))) ∧ p3))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234746382039113146645701124953 : ((p4 → (p1 → p2)) → ((((((((p4 ∨ p4) → False) → (p5 → (False → p4))) → True) → p4) ∨ p1) → p2) ∨ (False ∨ (p1 → (True ∧ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231349137835006226432256374501 : (((False → True) ∨ p1) → ((((True → p3) ∨ (p5 ∧ p4)) → ((True ∧ p4) ∧ ((p3 ∨ True) ∧ ((p5 → (p4 ∧ p3)) ∧ p3)))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135279871743402645467885799959 : (((True → ((p3 ∧ p4) → (False ∧ (p1 ∨ (p5 ∧ ((((p4 ∨ p4) ∧ p1) ∧ (p3 → p5)) ∧ True)))))) → (p4 ∧ p5)) ∨ (True ∨ (p2 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216695904044556105107864743555 : ((((True ∧ p3) → p1) ∧ True) → ((p4 ∧ (p3 ∨ ((p1 ∧ p2) ∨ ((p4 ∨ p5) → (False ∨ False))))) ∨ ((p1 → (p2 → p1)) ∨ (p2 ∧ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147640234353272867004245280094 : ((((False ∧ (p5 → (p2 ∨ ((p1 ∨ (((p1 ∨ ((False ∧ p3) ∨ p1)) ∧ p4) ∨ p5)) → p4)))) → p2) → p4) ∨ ((False → (False ∨ p1)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648354550188780128556332195845 : ((((((p2 ∧ ((p1 ∧ ((False ∧ (p5 ∨ ((True → p5) ∧ p3))) ∧ False)) ∨ (((False ∨ p2) ∧ p4) ∧ p5))) ∧ False) ∨ p1) ∧ (p4 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



