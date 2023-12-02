variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324179456608531719094244472248 : (p5 ∨ ((p4 ∧ (((p4 → (p4 ∨ p5)) → (False ∨ p2)) ∨ p1)) ∨ ((((p3 → p1) ∨ p5) → (False → p1)) → ((True ∨ p1) ∨ (False ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41366394274650567288017113382 : ((((((True ∧ (p4 → False)) ∧ (p3 ∧ (p2 → True))) → ((p3 ∨ p2) ∨ (p4 ∧ p4))) → ((p1 ∨ (False ∨ (p3 ∧ False))) ∨ False)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679042752958444050999942030891 : ((((False ∨ ((((p3 ∨ p1) ∧ p3) ∨ ((p4 ∨ (p3 ∨ False)) → p1)) ∨ ((p3 ∨ True) ∧ (p2 ∧ p5)))) ∨ (p3 ∨ (True → (p4 → True)))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324906560092870104868525728910 : (p5 ∨ ((p3 ∧ False) ∨ ((True → ((p1 → p2) → False)) ∨ (((p5 ∧ p2) → ((p3 ∧ p5) ∧ p4)) ∨ ((p5 ∧ p3) → ((p4 ∨ True) ∧ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50352272065915771951746401304 : (((((p5 ∧ (True ∧ p5)) ∨ p4) ∨ ((((((p5 → p5) → (p4 → p5)) ∨ False) ∨ p3) → p3) → p1)) ∨ (False → (True ∧ (False ∧ p3)))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803072733694015986368712414709 : (((p3 → (((p4 ∧ p2) ∨ ((((p5 ∨ True) ∨ p3) → (((p3 ∨ p3) → p3) → ((True ∧ False) → p2))) → ((p2 → p3) → p4))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113351368913383938144832009918 : (((p2 ∧ ((((False ∨ False) ∨ (False ∨ ((p2 ∨ p2) → (((p3 ∨ p2) → (p4 ∧ True)) ∨ False)))) ∨ p5) ∨ False)) ∧ (True ∧ False)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133987318074104493637232882967 : ((((((p3 ∨ p1) ∨ ((p3 ∧ (True ∨ (p1 → p3))) ∧ ((p3 ∧ True) → (p4 ∧ True)))) ∨ (p5 ∧ True)) ∧ p2) ∨ p2) ∨ ((p4 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256637670479692038410266346025 : ((p1 ∨ False) → (((p3 ∨ (((p2 → (((p3 → p5) ∧ p1) ∧ p3)) ∨ p5) ∧ (p4 → (p4 ∧ (((p5 ∧ p5) ∨ False) ∧ p2))))) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219816891807595076339035634566 : ((p3 → ((False ∨ True) ∧ False)) → (((((p5 → False) ∨ (True → ((p2 ∧ ((p5 → (p3 ∨ (p3 ∧ p5))) → p1)) ∨ p5))) → False) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48980386750683476130945999950 : ((((((p1 ∧ ((True → True) → p5)) ∨ ((p4 ∧ p5) → p4)) → ((False → p4) → (p4 → (p5 ∨ p3)))) ∨ False) ∨ ((p3 ∧ p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117652104110248804533455508994 : ((p3 ∧ (((True → (((p5 ∧ (((p2 ∧ p1) ∨ False) ∧ ((True → p4) ∨ p1))) → (False ∧ p4)) ∨ True)) ∧ p5) ∨ (False → False))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57731154303929306884539083633 : ((((p2 ∨ p4) → p1) → (((p3 → p5) → p4) ∨ (False → (((True → ((True → p2) ∨ (p5 → (False → True)))) → p4) → (p5 → p4))))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716825393364764008262453631948 : ((((False ∧ (p1 ∨ (p4 → p2))) ∧ (p3 ∧ ((p3 ∨ False) ∧ (((p2 → (((p1 ∨ (False ∧ p3)) → (p5 ∨ p3)) ∨ False)) → True) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111167291159826167373657291389 : ((((p3 ∧ ((p1 ∧ True) ∨ p1)) ∧ ((p3 ∨ (((p3 → p5) ∧ ((False ∧ p1) ∨ p2)) ∨ ((False → p5) → p5))) ∨ False)) ∧ p1) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259488285394692602911726647479 : ((False → p5) → ((((((p2 → False) ∨ False) → (p4 ∨ False)) ∧ p3) ∨ (((((p4 ∧ (True → p1)) ∧ True) → p4) ∨ p4) ∨ (p2 ∧ p3))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612893422125248841569666544549 : (((((False ∨ (p4 ∨ (((((p2 → (p3 ∨ (False ∧ False))) ∧ ((p5 ∧ False) ∨ p3)) ∧ True) ∨ p2) ∧ (p4 → p4)))) ∨ (p3 ∨ False)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_720550918821986288852049176117 : (((((p4 → (True ∧ p4)) ∨ True) → ((((((p4 ∧ (p4 ∨ p2)) ∨ (p1 → True)) ∨ True) ∧ (True ∨ (p4 → p1))) ∧ p5) ∨ (p3 → p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46526238762992539563851175106 : ((((False ∧ p2) ∨ ((p5 ∧ ((((p5 ∨ True) → (False ∧ p4)) ∧ (p4 → (p2 ∧ ((p5 ∨ True) → p3)))) ∧ p1)) ∨ p4)) ∧ (p2 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304120596734285615921339718736 : (p1 ∨ ((p4 → (((p1 → (((True ∨ (True ∨ p3)) ∨ ((p4 → True) ∧ p5)) → p3)) → True) → ((p2 ∨ (False ∧ p2)) ∨ (p3 ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218616437179939611081065458907 : (((p5 → p2) → (p3 ∧ p4)) → ((p2 → (((((False ∧ False) → p1) ∧ p1) ∧ p4) ∧ ((p2 ∧ ((p4 → p3) ∧ (p5 ∨ p2))) → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183770981464846022665322188546 : ((((((((p5 → p3) ∨ p1) ∨ p3) → p1) ∨ p3) ∧ p4) ∧ p5) ∨ ((True ∨ p2) ∨ (p2 ∧ (((p3 → p5) → (p3 → p2)) ∧ (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786249359229845440583062116113 : (((p4 ∨ ((p5 ∨ (p2 ∧ ((p5 ∧ (False ∨ ((p1 ∧ p4) ∨ ((p2 ∨ p4) ∨ p2)))) → (False ∨ p1)))) ∧ ((False → (p2 ∧ True)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66479767718713768653155562487 : ((True → (((((p5 ∧ (p5 → (((True ∨ (True → p4)) ∨ p1) ∨ (True → p5)))) → p3) ∨ (p5 ∨ ((p2 ∨ p2) ∧ p4))) → p1) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178554163974191676752415117216 : (((((False ∨ True) ∨ (False → p3)) ∨ False) ∧ ((p4 → (p4 → True)) → False)) ∨ ((False ∧ (p2 ∨ ((p2 ∨ p1) → (p5 ∨ (True ∧ p1))))) → p5)) := by
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
theorem thm_5_vars_119223004307405888572793552309 : ((p2 → (((False ∨ p1) ∧ p3) ∨ ((((p5 → (((p4 ∨ (p3 ∨ False)) ∧ False) → p4)) ∧ p4) ∨ (p5 ∨ (p4 ∨ p4))) ∨ p2))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66067667866571462978164785227 : ((p5 ∨ ((((p1 ∧ (False ∨ (p5 → p5))) → p3) → (p2 ∨ ((True ∨ (((True ∧ True) ∧ p5) ∧ (p5 → p2))) ∧ (p2 ∨ p4)))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207035093103619120053519668471 : ((((p3 ∨ p2) → (False ∨ p3)) ∧ p3) → ((p4 ∨ ((True → p4) ∨ ((p4 ∧ (True → p1)) ∧ ((p4 ∨ p2) ∨ ((True → p2) ∧ p4))))) ∨ True)) := by
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
theorem thm_5_vars_112875382259095048324037806017 : ((((p1 ∨ (p3 ∨ True)) → ((((p3 ∨ p1) ∨ p4) ∧ (False ∨ p2)) → (True ∧ (p5 ∨ ((False → p1) ∨ (False → p5)))))) → p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47071671529701756633049036245 : ((((p2 ∨ (((p3 → (p4 ∨ (p2 ∧ (((False → p4) ∧ p1) → p4)))) ∧ (p3 → True)) ∨ (p1 ∨ p5))) ∨ (p4 → p4)) ∨ (p4 ∧ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39858646323594183582800757209 : (((p1 → (p2 ∨ ((p4 → ((p4 ∨ p3) ∧ (((p4 ∨ p2) → ((p1 ∧ True) → True)) ∨ ((p5 ∨ p3) ∧ p5)))) → (p5 → p3)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736944062864205396568736853037 : ((((p3 → True) ∧ (((p4 → ((p3 → (False ∨ p5)) ∨ p3)) ∧ (True → p3)) ∨ ((p1 ∨ ((False ∧ p4) → p4)) ∨ ((True ∨ p3) → p5)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325093378516567773496136704553 : (p5 ∨ ((p1 → p2) → (((((True ∨ False) → p1) ∧ p2) ∨ (p3 → ((p4 → (True ∧ (True → (p4 → (False ∨ (True ∧ p4)))))) ∨ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_469266113634564077032837546162 : ((((((p5 ∧ p4) ∧ True) → (((((p2 → p3) ∧ False) ∧ p4) ∨ True) ∨ True)) → ((p2 ∨ ((p1 ∧ (p3 → p4)) ∨ (True → p3))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_804586805958312452873416264737 : (((p3 → (((False ∧ (p1 ∨ True)) ∨ False) ∧ ((p4 ∨ (True → ((False ∨ (p5 ∨ True)) ∧ True))) ∨ ((True → (p3 ∨ p3)) → (p2 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798249316802177176791654910047 : (((p1 → (((((p5 ∧ True) ∨ (False → True)) → (p2 ∧ (p5 ∧ ((p4 ∨ False) ∧ p3)))) → False) ∨ (((p1 ∨ (False → p5)) ∨ p3) → True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152640029870214484598577736334 : (((p4 ∨ p4) ∧ (p5 → ((p1 → (p3 → (True ∧ (p3 ∧ (p2 ∧ (p1 ∨ (False ∨ p3))))))) ∨ (p3 ∨ p4)))) → (True → ((p5 → p1) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326162449957289583236485848258 : (p5 ∨ (p2 → ((p3 → (p2 ∧ ((p3 → ((p3 → (p4 ∨ (p4 → False))) ∨ p4)) → (((p5 ∨ (False ∧ (p3 ∧ p1))) ∧ p4) ∨ True)))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112213624005445529602310811130 : (((False ∨ ((p2 → p2) → ((False ∨ (p5 ∨ True)) → (((False → p3) ∧ (False → True)) → (p1 ∨ ((p1 ∨ False) ∨ p4)))))) ∨ p2) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781023733382876592292848083402 : (((p2 ∨ ((p5 ∧ p4) ∧ (p3 ∧ ((p1 → (p2 → (((p1 ∧ p2) → (False ∨ p2)) ∧ True))) ∨ (True → (True ∧ ((p4 ∨ False) ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185541660075719449950265798904 : ((p3 ∨ (p4 ∨ (((p4 ∨ p2) → (p3 ∧ True)) ∧ (False ∨ p2)))) ∨ ((p2 ∨ ((p2 ∧ (False ∧ (p3 ∧ ((p1 ∨ False) → p2)))) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180879116207921057376398348685 : ((((True ∨ p4) ∧ True) → (((p5 ∧ False) → p4) ∧ ((p4 → p4) ∧ True))) → (p5 ∨ ((p4 ∨ (((p1 ∧ p1) → False) ∨ p5)) ∨ (False → p4)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354039497647401077142129133847 : (p4 → (p4 → (((((p5 ∧ p3) ∨ (False ∧ p1)) ∨ False) ∨ (True ∨ ((p4 → False) ∨ True))) ∨ (p4 → ((p1 → (False ∨ (p2 → p2))) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759833927136180471626239082986 : (((p2 ∧ ((((p2 ∧ p4) ∧ p1) ∧ ((p5 ∧ p1) ∧ False)) ∨ (((False ∧ True) → True) → ((((False ∨ p5) → (True ∧ p2)) ∧ False) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310158545145532749934418891303 : (p2 ∨ (((p5 ∨ True) ∧ ((((p4 → p2) → ((p4 ∧ p4) ∨ p2)) → p2) ∧ p4)) → ((p1 ∧ p3) → ((False ∧ ((True → p1) ∧ True)) ∨ p2)))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 → p2) → ((p4 ∧ p4) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h6.left
    let h15 := h6.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : ((p4 → p2) → ((p4 ∧ p4) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137193456942485507854117995272 : ((False ∧ ((p1 ∨ p1) → (p5 → (((((True ∨ p4) ∨ p2) ∧ ((False ∧ (p3 ∨ p2)) → True)) → p1) → (p3 → False))))) ∨ (True ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208301814531707011153115340706 : (((p4 ∨ p4) ∧ ((p3 → p2) ∨ True)) → (((p4 ∧ ((p4 ∨ p2) → p1)) → (((p4 ∧ p2) ∨ p3) → ((False ∨ p5) → p3))) ∨ (p1 → p1))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622621661132807517079307492888 : ((((p4 ∧ ((((p2 → (True ∨ (p1 ∧ ((False ∧ ((p1 ∨ p1) ∧ p1)) → p4)))) ∧ (p2 ∧ (False ∨ False))) ∧ p3) ∨ (p1 ∧ p5))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_113954246408699715424853275909 : ((((p1 ∨ p2) ∧ (False ∨ ((p1 ∧ ((p4 ∧ p5) → p3)) ∨ (p5 ∧ (p1 ∧ (False → (False → p3))))))) ∧ (p5 → (p4 ∨ p1))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148187136555971061831880372571 : (((((True ∧ (p5 ∧ True)) → (p4 ∧ (p1 ∨ p2))) ∨ ((p5 ∨ p1) ∨ (False ∧ p3))) ∧ ((True ∨ False) → p4)) ∨ (((False ∧ p2) → p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164539715797618451375268767383 : ((((p5 → ((p2 ∧ ((p5 → p2) → (True ∧ p5))) ∧ p2)) → ((True → p3) ∧ False)) ∧ p4) ∨ ((False → p5) ∨ ((p5 ∧ (True ∧ False)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147150158254772430174303917815 : (((p2 ∧ (((p3 ∧ ((False ∧ p2) ∨ p2)) → p3) → ((p4 ∨ (p5 → (p1 ∧ p5))) → (p5 ∧ p2)))) ∧ p3) ∨ (False → (p5 ∨ (False ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221469370305275572967521799303 : (((p1 → True) ∨ p1) ∧ ((p1 ∨ ((((False → False) ∨ p2) ∧ True) ∧ ((p1 → ((p4 ∧ True) ∨ p2)) ∨ (p2 ∧ p1)))) ∨ ((p2 ∨ p2) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_675699267392330934558224087963 : (((((((False ∨ ((p1 → ((False → p4) ∨ (p4 → True))) ∧ p1)) ∨ True) ∧ p3) ∧ (p3 ∧ (p2 ∧ p5))) ∧ (True ∨ (True ∧ (p1 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262247364424060502887932111734 : (True ∧ (((p2 → ((p5 ∨ (((p2 ∨ p4) → (p4 → p4)) ∨ (p3 ∨ p1))) → ((p3 ∨ p5) → ((p4 ∨ p2) ∨ p2)))) → (False ∧ True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37555272730929037878043063492 : ((((p1 ∨ ((p5 ∧ p4) ∧ ((((p4 ∧ ((p5 → (p3 ∨ (p4 → p5))) ∧ (True ∧ False))) ∨ (p1 ∨ p1)) ∨ False) ∨ True))) ∨ p3) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729831156253989295216850514151 : (((((False ∧ True) → False) → (((p3 ∧ False) ∨ ((p3 ∨ p1) → (True ∧ (True ∧ False)))) ∨ (True → (p2 → (False → ((p5 ∨ p4) → True)))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712608250692348363755198206417 : (((((p3 ∨ (False ∧ False)) → (p1 ∧ p1)) ∨ ((((False ∧ True) ∨ (((False ∨ ((p2 ∨ p2) ∧ p3)) ∧ p3) ∧ (False ∨ True))) ∨ p3) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601501842826041280654417484304 : ((((p3 ∧ ((p1 ∧ (((p1 ∧ (p3 ∨ ((False → (True ∧ p1)) ∧ (p4 → ((p4 ∨ True) ∨ True))))) ∨ p3) ∨ (p2 ∨ p5))) → p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151245784506234143348566196803 : ((((False ∨ False) ∨ (p2 ∨ ((False ∧ (p5 ∨ ((p2 ∧ ((p4 → (True → p3)) ∨ p2)) ∧ p3))) → p5))) → p3) → (p4 ∨ ((p4 ∧ p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ False) ∨ (p2 ∨ ((False ∧ (p5 ∨ ((p2 ∧ ((p4 → (True → p3)) ∨ p2)) ∧ p3))) → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65184431182398458503493141958 : ((p3 ∨ (((p4 → p1) → (((p4 → ((p4 ∨ False) ∧ ((p1 → (((p4 ∨ p4) ∧ True) ∨ p4)) → False))) → (False ∨ p3)) ∨ True)) ∧ True)) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610037821037091572708262018185 : (((((((p2 → (((p2 ∧ ((p2 → False) ∧ (False → (False ∨ (False ∨ p4))))) ∨ (p2 ∧ p1)) ∧ p1)) → (p5 ∧ p2)) ∧ p4) → False) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56614470725451253611429397384 : ((((True ∧ p4) ∧ p3) ∧ ((((((p2 ∨ p5) ∧ p5) ∨ p4) ∨ p4) ∧ p5) → (True → (p3 ∨ ((p5 → ((p3 ∧ p3) ∧ p4)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691684634581281057006592111187 : ((((True ∨ (((p4 ∧ (False ∨ (False ∨ (p2 → p1)))) ∧ (p1 ∨ False)) ∨ (p5 ∨ False))) → ((p4 ∨ p2) ∧ (p1 → ((p3 ∨ p4) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299314786109982007581384150185 : (False ∨ (((p3 ∧ ((p2 ∨ (False → p5)) ∧ True)) ∧ (True ∧ ((p4 ∧ False) ∨ (((p1 ∨ ((p1 → (p2 → True)) → True)) ∧ p1) ∨ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208251230557491187261336231004 : (((p3 ∧ p3) ∧ ((p2 → p2) → False)) → ((p3 → True) ∧ ((True ∧ (((p5 ∨ p1) ∧ ((p1 ∧ p3) ∧ (p2 ∧ p2))) ∧ True)) ∨ (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737684719079223879664548162574 : ((((p5 → p4) ∧ ((((((p5 ∧ ((p4 ∨ p3) ∧ (p4 ∨ (p2 ∧ False)))) → (p4 ∧ p2)) → p2) ∨ p4) → (p4 ∨ p5)) ∨ (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52384910792417652515990234318 : (((((((p1 ∧ True) → p1) ∧ True) → p5) ∧ (p4 ∧ (p5 ∧ (p4 → False)))) ∧ (((p1 ∧ ((p3 ∧ False) → (p2 ∧ p1))) ∨ False) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346326536653663461734169371003 : (p3 → (((((p4 → ((p4 → (p2 ∨ p1)) → p2)) → ((p2 ∨ False) → p1)) ∧ (False → (False ∧ p3))) → (True → (False ∨ p1))) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303764833021505728787037330437 : (p1 ∨ (((((p1 ∧ p1) → (False ∧ (p1 ∧ p1))) ∧ (((p5 → True) ∨ (((p5 → (p3 ∨ p3)) ∨ True) ∨ (p5 → p4))) → p2)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137162614192756322083992083684 : ((False ∧ (((((p3 ∨ p5) → (p2 ∧ (p4 ∧ p1))) ∨ False) → (p4 → ((p3 ∧ p3) → ((p4 ∧ p2) ∧ False)))) → p3)) ∨ ((p1 → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689645281372011649784870667 : (((False ∨ (True ∧ ((p5 ∨ p3) ∧ ((p4 ∨ (True ∨ p3)) ∧ (p4 ∨ False))))) → (p2 ∨ ((p3 ∨ (p4 ∨ (p3 ∧ True))) ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- False on the left can always be used.
            apply False.elim h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h20 =>
            -- False on the left can always be used.
            apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h7.left
      let h23 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h26 =>
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h30 =>
            -- False on the left can always be used.
            apply False.elim h30
        case inr h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h33 =>
            -- False on the left can always be used.
            apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346283108966298924186591970009 : (p3 → (((((((p1 ∨ ((False ∨ p4) ∨ (p2 ∨ p3))) ∨ p5) → (True ∧ (False ∨ p1))) → (False ∧ p5)) ∧ (False ∧ True)) ∧ p1) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245327560207567497536946178781 : ((p2 ∧ p2) ∨ (p3 ∨ (((p2 ∧ (((p4 ∧ p4) → p2) ∨ ((p4 ∧ (((p5 → p4) ∨ p3) → (False → p4))) ∨ p1))) ∨ p5) ∨ (p4 → True)))) := by
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
theorem thm_5_vars_171852582994474445407928362983 : ((((p4 → p5) ∨ (p4 ∨ (((((p5 → False) ∨ False) ∧ p4) ∧ p3) ∨ True))) → p3) ∨ ((((p5 → p3) ∨ (True ∨ p1)) ∧ (False → False)) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317001241072966934891900528802 : (p3 ∨ (p3 → ((((False → p2) → p5) ∧ p1) ∨ (p2 → ((p5 ∧ (((p5 ∨ p3) → (p4 ∧ (((False → p3) ∧ p2) ∧ True))) ∧ p2)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238014237784165778725567040772 : ((True ∨ p1) ∧ ((p4 → ((p2 ∧ (p4 ∧ ((p1 ∨ (False → p1)) → ((False ∧ p1) ∨ p3)))) ∧ p2)) ∨ ((p4 ∨ ((p5 ∨ True) ∧ p4)) → p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57124918208108248557210740736 : ((((p5 ∨ p4) ∧ False) ∨ (p2 ∧ ((((True ∧ p1) ∧ p1) ∨ ((p1 ∧ (p2 ∨ ((p2 → p4) ∧ True))) ∨ (p1 ∨ (p3 ∨ True)))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187022054021222949925695489138 : (((p2 ∨ (p2 → p4)) → ((p2 → p3) ∨ ((p3 ∧ p2) → False))) → (p1 → ((p3 ∧ (p4 → ((False ∨ p5) ∨ (p3 → p1)))) → (p3 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82211666803438952157833099989 : (((((p4 ∨ (p3 ∧ (p4 ∨ (((((False ∨ False) ∨ p2) ∧ p5) ∧ p4) → (True ∨ p4))))) → p5) ∧ p1) ∧ ((p3 → (p2 ∧ False)) ∧ p3)) → False) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299500735469097068904179173985 : (False ∨ ((p5 → (((p2 ∧ (((p1 ∧ (True → p3)) → (((p2 ∧ (((True ∧ p3) ∨ p1) → p5)) ∨ p5) ∨ p1)) → True)) → p4) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340089010161332295969684545164 : (p1 → (p3 → ((((p3 ∧ (p2 ∨ (((p2 → True) ∧ p2) ∨ p3))) ∧ (((False → (p3 ∨ False)) ∧ p3) ∧ p4)) ∨ ((False ∨ False) ∧ p3)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661292273734772499949776173191 : (((((((p5 → (p4 ∧ (p1 ∧ ((p4 → (p5 → (p1 → False))) ∨ (True ∧ (p3 → True)))))) → False) ∨ False) → (p1 ∨ p4)) → (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341915491112431775294909889400 : (p2 → (((((p1 ∨ ((p5 ∨ ((p2 ∧ ((False → False) → p1)) ∨ p1)) → p5)) ∨ (p5 ∨ p1)) ∨ p4) → (False ∨ p2)) ∧ ((False → p2) ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h6 =>
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
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234461381514045753465536537031 : ((p2 → (True ∨ p4)) → (((p5 ∧ False) → p1) → (((((p5 → p4) ∨ (False → ((p4 ∧ True) → p1))) ∨ True) ∨ False) ∨ ((p4 → False) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47080305158322489734849647746 : ((((((p4 ∧ p4) ∧ (((True ∧ ((p2 ∨ (False ∨ p1)) ∧ p3)) ∧ ((p3 → p4) ∧ p5)) ∨ p5)) → p2) → (p4 ∨ False)) ∨ (p5 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586550156532211359769275682863 : ((((((p4 ∨ True) ∧ ((((True → p1) → p2) → (((p5 ∧ False) → (p3 ∧ p2)) ∨ ((p4 → p4) → (p4 ∧ p4)))) → p1)) ∧ True) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617453840941972458604164604522 : ((((((p4 ∧ ((p3 ∧ p2) ∧ p1)) ∧ False) ∧ (p2 → ((((p3 ∧ p3) ∨ (p4 ∨ p5)) → (False ∨ (p5 ∨ (p4 ∧ False)))) → True))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43747438522182883812067468347 : ((((True ∧ (((p1 → (p1 ∧ p4)) ∨ (p5 → (p5 ∧ (p4 → ((p2 ∨ (((p3 ∧ True) → p5) ∧ p2)) → p3))))) ∨ p1)) → p3) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135578029672082445166194426802 : (((((p4 ∧ False) ∧ (((p4 ∧ p1) ∧ p1) ∧ ((p1 ∧ p5) → (p4 ∨ p4)))) ∨ p2) ∨ (p2 ∧ ((p3 → False) ∨ p5))) ∨ ((True ∧ False) → p4)) := by
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
theorem thm_5_vars_112677078126786164451233057960 : ((((((False ∨ (p3 ∨ (p2 ∨ p1))) ∨ False) ∧ ((False → ((p4 → (p4 → p2)) → p1)) → p2)) → ((p4 ∧ True) ∨ p5)) → p2) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136153932913462567769071714729 : ((((False ∨ p5) → (p3 ∨ ((True ∧ p3) ∨ p1))) → (((p5 ∧ (True ∧ p3)) ∨ p5) → (p1 ∧ (p1 → (p3 ∧ p1))))) ∨ ((False ∧ False) → False)) := by
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
theorem thm_5_vars_201207883877280204643540505101 : ((p2 → ((p3 ∧ ((p4 ∧ p2) ∧ p1)) ∧ p4)) → ((p1 ∨ (p5 ∨ True)) ∨ ((((True → (p5 ∨ p3)) ∧ False) → False) ∨ ((True ∨ p5) ∧ p4)))) := by
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
theorem thm_5_vars_42489424467684086761643850488 : (((False ∨ ((((True ∧ (((False ∨ True) ∨ False) ∨ (((p1 ∨ ((True → p3) ∧ p4)) → (p2 ∨ p2)) ∨ p4))) ∧ p1) ∧ p2) ∨ p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48143369423361710257666101164 : ((((p5 → (True ∧ True)) ∨ (((p1 → p2) → (p3 → ((p4 ∧ p2) ∧ (p5 ∧ (True → p4))))) ∧ ((p4 → p4) ∧ p3))) → (p4 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42551349745831148917952508286 : (((p1 ∨ ((p5 → p5) ∧ ((False ∨ ((p1 → p5) ∧ p3)) ∧ (p1 ∧ ((p5 → (p5 → (p5 ∨ (p1 ∨ p5)))) ∨ (p1 ∨ p5)))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977659346678851359158205991988 : (((True ∧ (((False → True) → False) ∧ (((((p5 → False) ∨ False) → (p2 → p5)) ∨ p3) ∨ (False ∧ (False ∧ ((p2 ∧ (True ∨ p1)) → p3)))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h8
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h12
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48857276392379796193770033725 : (((p3 ∨ ((p4 ∧ (False ∨ False)) ∧ ((p5 → (((((p1 ∧ p5) ∧ p1) → (p1 ∧ p1)) → p3) → p2)) ∨ p4))) ∧ ((p3 ∨ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46362744026487457066944348273 : ((((True → ((((p1 ∨ p1) ∨ (True → p2)) ∧ (p2 ∨ p4)) ∧ False)) ∧ (((p4 ∧ p3) ∨ (p2 → (p3 ∧ p3))) ∨ True)) ∧ (False ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4206499473165703148973023383 : (p5 ∨ (((((p2 ∧ (((p1 → True) ∨ p2) ∧ (((p2 → p1) ∨ p3) ∨ (False → p4)))) → p3) → p5) ∨ (True ∧ (True ∨ True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



