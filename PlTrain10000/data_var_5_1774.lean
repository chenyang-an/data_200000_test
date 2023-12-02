variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136056128596926117459347279210 : ((((p3 ∨ (p5 ∧ ((p5 ∨ p3) ∨ p4))) ∨ True) ∧ ((p4 ∧ True) ∧ (p5 ∧ (((p3 ∨ (p1 ∨ False)) → p5) ∧ p4)))) ∨ ((p5 ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168426004704553711775696072267 : (((True ∨ p3) → (p4 ∧ ((True → ((p1 ∧ (((p2 → p2) ∨ p3) ∧ p2)) → False)) → p2))) → ((False ∨ (p3 → p1)) ∨ ((p2 ∨ True) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200367352645378219398435082784 : (((p2 → p3) ∧ (((p4 ∨ p5) ∨ False) ∧ p3)) → ((p5 ∨ p5) → (p1 ∨ (True ∧ ((p1 ∨ (p4 ∧ (False ∨ (p5 → p5)))) ∨ (False → p3)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56174843110875767834907020999 : (((p2 ∧ ((False ∨ p4) → p2)) ∨ ((p2 ∧ ((p3 ∨ p3) ∨ (((p3 ∧ p3) ∨ False) ∨ ((p3 → (p2 ∨ p5)) ∧ (p1 → False))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135756869297458521621703352935 : (((p4 ∧ ((((p2 → p1) ∨ p5) → (p3 → False)) → (True → (p4 ∨ False)))) ∨ (p3 → ((p5 ∧ p3) → (True ∨ True)))) ∨ (p5 ∧ (p4 ∨ True))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46933528894821186387543486986 : ((((False ∧ ((((p2 ∨ (p2 ∧ (((True → p5) ∨ p4) ∨ (True ∨ p1)))) → (p1 ∨ (p4 → p3))) ∨ False) → False)) ∨ p2) ∨ (p3 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692880565617609701544550958466 : (((((p3 → (p1 ∨ p3)) → ((((p5 ∨ (p4 ∧ p1)) → False) → p2) ∨ False)) ∧ (p1 → ((p3 → ((p2 ∧ p4) ∧ p5)) ∧ (True ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52290233563898627370287546213 : ((((((p1 ∧ ((p3 ∨ p3) → (False ∧ p5))) → (p3 → p2)) ∧ p1) ∧ p5) ∧ ((((p2 ∧ (False ∨ p2)) → p4) → (p4 ∨ p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234597682336230890244689444895 : ((p3 → (p3 ∨ True)) → (((((((p3 ∧ ((p4 ∨ (False → p2)) ∧ (p1 → p4))) ∨ p4) ∧ True) ∧ p3) ∧ (p4 ∨ True)) ∧ p2) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47031552820341630527735449370 : ((((((((p2 ∨ True) ∨ True) → ((True ∨ (p5 ∨ (p3 ∨ (p3 ∧ (p3 → p4))))) → p1)) ∨ p3) ∧ True) ∧ (p2 ∨ True)) ∨ (True ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2026829531703915063946644975 : ((p1 → ((p4 ∧ ((p1 ∧ p5) ∧ (False ∨ False))) → (((p3 ∨ p4) → p5) ∧ (p2 → (p3 ∧ p4))))) → ((True → p2) → (p2 ∨ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135610127087806387524035015033 : (((p2 ∧ ((True ∧ (True → (p1 ∨ (p3 ∧ (p5 → ((p1 ∨ True) ∧ p5)))))) → p3)) ∨ (p5 ∧ (True ∧ (p1 ∧ p5)))) ∨ ((p4 → True) ∧ True)) := by
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
theorem thm_5_vars_149186178091483931195114728573 : (((p1 → p5) ∧ ((p1 → (p3 ∨ ((((p1 ∧ p4) → p4) ∨ ((p2 → p4) ∧ (p5 → False))) ∧ p5))) ∧ p4)) ∨ ((p1 ∨ (True ∨ False)) ∨ False)) := by
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
theorem thm_5_vars_147435778275125207858681370912 : ((((p2 ∧ True) ∧ ((p1 → (p5 ∨ ((False ∧ (p4 ∨ p4)) ∧ False))) → ((p5 ∨ (p4 ∧ p4)) → p1))) ∨ p1) ∨ (False ∨ (p4 → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134169019952040958673552827376 : (((((p1 → (((True ∧ (p3 ∧ p4)) ∨ (p2 ∧ (p3 ∧ p1))) ∧ False)) ∨ p3) ∨ ((True → p2) ∧ (True ∨ p3))) ∨ True) ∨ ((p3 ∨ True) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305423213639263922961919587103 : (p1 ∨ ((p3 → (p3 ∧ (p4 → ((((p2 ∧ p2) → p2) → p4) → ((p4 ∨ p5) → False))))) ∨ (True ∨ ((((p5 ∧ p3) ∨ p5) → True) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148294332821059560054651676973 : ((((((((p3 ∧ True) ∨ p4) ∧ p4) → p3) → p2) ∧ (p4 ∨ ((p4 ∧ p5) → p3))) → (p3 ∧ (p3 ∧ True))) ∨ (((p3 ∨ False) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62643407953315158097128009688 : ((p4 ∧ ((p3 → ((p4 ∨ (((p1 ∨ (((False → p2) ∧ p4) ∧ (p2 ∨ (p4 → p2)))) ∨ (p4 → (p2 ∨ p1))) ∧ p2)) ∨ p1)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91023499153293365143921459011 : (((p1 → p4) ∧ (True ∧ ((((((p3 → p2) ∨ (False → (p1 ∨ (False ∨ ((False → p5) ∧ False))))) ∧ False) ∨ p4) → p1) ∧ (p4 ∧ p3)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : ((((p3 → p2) ∨ (False → (p1 ∨ (False ∨ ((False → p5) ∧ False))))) ∧ False) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615328964740376299562823120825 : ((((((False ∧ ((True ∧ (p1 → False)) ∧ ((False ∨ False) ∧ (p5 ∧ False)))) ∨ (p2 ∨ True)) ∨ (p2 → (p5 ∨ ((True ∨ p2) ∨ p5)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53156434707352187238305150383 : ((((((p4 ∧ p4) → p3) ∨ ((p3 → (p5 ∨ False)) → p3)) ∨ False) ∨ ((False → ((False ∨ (p3 → (p2 ∨ p3))) ∧ (p2 ∨ p4))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670115202147478393938448224114 : ((((((p1 ∨ (p3 ∧ (p5 → p4))) ∧ p2) ∨ (((p1 ∨ (p2 → p1)) → (p2 → ((p2 → p2) → p1))) → p4)) ∨ (p2 → (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657227635599934646187750511212 : (((((True ∧ (p2 ∨ p5)) → ((p4 ∨ (p4 ∧ ((False ∧ (False ∨ (p2 ∨ False))) ∨ (True ∨ (p4 ∧ False))))) → (p2 ∧ p5))) ∨ (p1 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165154887809123829192273632795 : (((((p5 ∨ (p1 → (True → p2))) → False) → ((p5 ∨ p2) → (p5 ∨ p5))) ∧ (p5 ∧ p4)) ∨ ((True ∧ True) → ((p4 ∨ True) ∨ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_821867726606617980991689414 : ((p4 ∧ ((((False → (p2 → (True ∧ p5))) → (p5 → (((True ∨ (p4 ∧ p3)) → (p3 ∧ (False ∨ p5))) → False))) ∨ p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45921053812477644498748207556 : (((p4 → ((p5 ∧ p3) ∨ ((((p3 ∨ False) ∧ p2) → (p1 → (p1 ∨ ((p4 ∨ p1) ∧ p4)))) → (p5 → (False ∧ (True ∧ p1)))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677502473998989606557585453626 : ((((((p4 ∨ p1) ∧ (((((p1 ∨ (p5 ∨ p4)) ∨ (True ∨ p2)) ∨ (False ∨ p2)) ∨ p1) ∨ p2)) ∨ True) ∨ ((p4 → (p1 → p4)) → p5)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_61551502148474205481593000021 : ((p1 ∧ ((False → ((((p4 → p1) → p1) ∨ False) ∧ (p5 → p5))) → (((p4 ∨ (((True → True) ∨ (p1 ∧ p1)) → p1)) ∨ p4) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64343117636913000605170758594 : ((p1 ∨ ((p1 → (p5 ∧ ((((p1 ∧ False) → False) → (((p2 ∧ (True → (False ∨ p1))) → (True ∧ False)) → p3)) ∧ (p2 ∨ True)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214167807284375446294438269672 : ((((p4 ∧ p2) → False) → p4) ∨ (False ∨ ((p3 ∧ (False → (((p2 ∧ p5) ∧ p5) ∧ (p1 → p1)))) → (p3 ∧ (p5 → ((p5 ∨ False) ∨ p5)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190588515056634397804084428208 : ((((p1 ∨ p1) ∧ ((True ∧ p2) ∨ (False → p4))) → False) ∨ (False → (p1 ∧ (((p5 → p4) ∨ (p4 ∧ (p3 → p2))) ∨ (p3 → (p3 ∨ False)))))) := by
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
theorem thm_5_vars_330253672697439606881951351164 : (True → (False ∨ ((((((((p1 → p1) → True) ∨ p1) ∨ p3) → p5) ∧ p5) → ((True ∨ p1) → (p4 ∧ p4))) → (True → ((False ∨ p4) → p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53695007386394821342828084278 : (((p4 ∧ (True ∧ (((False → p5) → p1) → (p5 → p4)))) ∧ (((p2 ∧ p5) ∧ (p5 → (p5 ∧ p5))) ∨ (p4 ∨ (p3 ∧ (p5 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764328980985291809279314334226 : (((p4 ∧ (((((True ∨ p1) → p3) ∨ (True → ((p2 ∨ ((True ∧ True) ∨ p3)) ∧ False))) → (((p2 → p1) ∨ (p2 ∨ p2)) → p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17363777451826226276568311235 : (((p1 ∧ (((((p4 → False) ∨ ((p5 → p3) → (((p2 → False) ∧ p3) → p3))) → False) ∨ False) ∧ (p2 ∨ p4))) → ((p5 ∨ p2) ∧ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : ((p4 → False) ∨ ((p5 → p3) → (((p2 → False) ∧ p3) → p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h9
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h22 : ((p4 → False) ∨ ((p5 → p3) → (((p2 → False) ∧ p3) → p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h27 := h20 h22
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h29 : ((p4 → False) ∨ ((p5 → p3) → (((p2 → False) ∧ p3) → p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- Implications on the right can always be decomposed.
        intro h31
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- One of the premise coincides with the conclusion.
        exact h33
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h34 := h20 h29
      -- False on the left can always be used.
      apply False.elim h34
  case inr h35 =>
    -- False on the left can always be used.
    apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160609948765616491324439724142 : (((p4 ∨ (p4 → (((p2 ∨ True) ∧ (False ∨ p3)) ∧ False))) ∧ (True ∨ ((True ∨ (p2 ∨ p2)) ∨ p3))) → ((p4 → ((p4 ∧ False) ∨ True)) ∨ p2)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h10
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h22
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h25
      case inr h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h27
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45763868441272531061578832955 : (((False → ((p3 ∨ p5) ∨ (((p4 ∧ ((p5 ∨ p3) → p5)) ∨ p2) → (((p5 ∨ (True ∧ (p1 ∧ p2))) ∨ (True ∨ p5)) → False)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33417995970185582329430326715 : ((p4 ∨ ((((p4 → p2) → (p3 ∨ ((((p3 → p3) ∨ p4) ∧ p4) ∧ p1))) → False) ∨ (p2 → ((p2 ∨ ((p1 → True) → True)) ∨ p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661958710189274278196631253626 : (((((((p5 ∧ True) ∧ p2) ∨ ((p5 ∧ (p1 ∨ ((False ∧ p1) ∧ True))) ∧ p3)) ∨ ((p1 ∧ p1) → ((True ∧ p1) ∧ p5))) → (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49051096667966894299492486919 : ((((((((p4 ∨ (p4 → p2)) ∧ p4) → (p1 ∨ (False ∨ (p2 ∨ False)))) → p1) → (p4 → p3)) ∧ (p3 ∧ p5)) ∨ ((False ∨ p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37448163659619250024322651165 : ((((((((p1 → p2) → p3) → True) → ((((p1 → p3) ∧ p5) → True) ∨ p4)) → (p3 → (p1 → (p2 ∧ (p5 ∧ True))))) ∨ False) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305303044412437821279117011448 : (p1 ∨ ((((p4 ∨ (p1 ∧ False)) → ((p2 ∧ p5) ∧ p3)) → ((p5 → p2) ∨ (p4 → (False → p5)))) ∨ (((p1 ∧ True) ∧ (p1 ∧ True)) ∧ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54761107660819858962869116971 : ((((True ∧ p5) → ((p1 ∨ p5) ∨ (p3 ∧ True))) → ((p1 ∨ (((True ∧ (False ∨ True)) ∨ False) → False)) → (((p5 ∨ p5) ∨ p1) ∨ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∧ (False ∨ True)) ∨ False) := by
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
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618743193185339082253077282808 : ((((((True ∨ p2) → True) ∧ (((p2 ∧ ((False ∧ (True ∨ (p3 → p4))) ∧ ((True → p3) ∨ ((True → p4) → p2)))) ∧ p4) ∧ p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_746799299528180757356247205288 : ((((p3 ∨ p4) → (p3 ∨ (((p3 ∧ True) ∨ (p5 ∧ p2)) ∨ ((((p2 ∧ (p2 ∨ False)) → p1) → p3) ∨ ((p5 ∧ p2) ∧ (p2 → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347721680460256726299659300194 : (p3 → ((p3 ∧ (p2 ∨ True)) ∧ (((p1 → True) → (p5 ∧ False)) ∨ ((((False ∧ True) ∨ (False ∧ p1)) ∨ p1) ∨ (((p5 → p3) ∧ p2) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_608201283056998558660841177706 : ((((((p3 ∨ ((p4 ∧ p1) ∧ ((p1 → (p2 ∨ (p2 ∧ (((p4 → ((p5 → p3) ∨ p5)) ∧ p5) ∧ True)))) ∧ False))) ∧ p3) ∨ p2) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118258983920913915587668356525 : ((p1 ∨ ((((((True ∨ p4) ∧ (p1 ∧ (p4 ∨ p3))) ∨ (p5 ∧ p4)) ∨ p4) → p3) ∨ ((p5 ∧ ((True ∧ False) ∧ p1)) ∧ p4))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802807524767796638471926312320 : (((p2 → (p3 → (p4 → (((p3 ∨ False) ∨ p1) ∧ ((p5 → (((p1 → True) ∧ ((p2 ∨ (p1 ∧ p1)) ∨ (p4 ∧ False))) → p5)) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112558138437818539762569917847 : (((((False → p2) → ((False ∨ ((p2 ∨ ((p5 → True) ∨ (((True ∨ (p3 ∨ p4)) ∨ p4) ∨ True))) ∨ p2)) ∧ p3)) → True) → p1) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208795954780099202040428151597 : ((p2 ∧ (True → (p2 ∧ (p3 ∧ p4)))) → ((((((p2 ∧ p5) ∧ p1) → (False ∧ (p1 → p4))) ∧ p1) ∨ p2) ∨ ((False ∨ (p5 ∧ p1)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62093030232162816098928248904 : ((p2 ∧ (p4 ∧ ((((p4 → p2) → ((False ∧ (True ∨ p1)) ∧ p5)) ∨ ((p4 ∨ p3) → p3)) → (p2 ∨ (p5 ∨ ((p3 ∧ p2) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708463214704604701025093170061 : (((((p4 → ((p5 ∧ False) ∧ (True ∨ p1))) ∧ True) → (p2 ∨ ((False ∨ ((p2 → False) ∧ p1)) ∧ (False → (p4 ∧ (p1 ∨ (p4 ∧ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590994739244600596635963841923 : (((((p3 → ((((False ∧ (((p1 ∨ (p4 → True)) ∨ False) → (p2 ∨ (p5 ∧ (p3 ∧ p5))))) ∧ p1) ∨ (p2 ∨ p5)) ∧ p2)) → p5) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2925340494400270300450665867 : (((p3 ∧ p5) ∧ p2) ∨ ((((True ∨ True) → (False ∧ True)) ∧ ((p2 → ((p5 → False) → False)) ∧ ((True ∧ False) → p4))) → (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h13 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h14 := h9 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234079010207127307664046524748 : ((True → (p1 ∧ p4)) → (((True → p1) → False) → ((True → p3) → (((((((p5 ∧ (False → p5)) ∨ p4) → True) → p1) ∨ p3) ∨ p2) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38846025792913744542098853290 : (((((p2 → False) ∨ False) ∧ (p4 ∨ (((False ∨ (p1 ∨ ((p4 ∨ ((((p1 ∧ p3) → p2) ∧ p3) → p3)) ∧ False))) ∨ False) → p2))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172563279587066099020015238789 : (((p5 ∧ (p2 ∨ False)) ∨ ((True ∧ (p4 ∨ (((p1 ∨ p4) ∧ p5) ∧ False))) ∨ True)) ∨ (((p2 → p4) → False) ∨ (p3 ∨ ((True → False) → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635107057012471469543221659779 : ((((((p4 → ((p5 ∨ ((False ∧ (p5 ∨ p2)) ∧ p5)) ∧ p2)) ∨ ((p5 ∨ (p5 ∧ p4)) → (p3 ∧ p4))) → (p4 ∨ (p1 ∧ False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147156152725841471087310848425 : (((p3 ∧ (p3 ∨ (p4 ∨ ((p2 ∧ ((((((False ∨ False) → p3) → True) → p3) ∨ p3) ∧ p4)) → p3)))) ∧ p2) ∨ ((p5 ∧ (True ∧ False)) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47020458533071542941474042377 : ((((p2 ∨ ((False ∧ (True ∧ p5)) → ((p5 → ((True ∧ ((p1 → (p3 → p1)) ∧ p1)) ∨ (p2 ∨ p2))) → p4))) → p1) ∨ (True ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45292400092846761256746387176 : (((p2 ∧ ((False ∨ p3) → (((p4 → (p2 ∨ ((p1 ∧ True) → (p2 → (p4 ∨ p4))))) ∨ (True ∨ ((p1 ∧ p3) ∨ p5))) → p1))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715787434350572878445591303409 : ((((((False ∧ p4) → p3) ∨ False) ∧ (((True ∨ (False ∨ p4)) → ((True → p2) ∧ False)) → (p5 ∧ ((((p2 → p2) → p5) → False) ∨ False)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ (False ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (True ∨ (False ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157485814880035747495265749336 : (((((False → False) ∧ (False ∨ ((p4 ∨ False) ∨ p5))) ∧ ((False ∧ (p5 ∧ p2)) ∧ p3)) ∨ (True ∨ p4)) ∨ ((p1 → p3) ∨ ((False ∨ p5) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50791823789442178856848352462 : (((True → ((((p3 → (p1 ∧ True)) ∧ ((p5 ∧ p2) → (p2 → True))) ∧ (p5 ∧ (p4 ∨ False))) ∧ False)) → (((p3 ∨ p1) → p5) → p2)) ∨ p5) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156943187136149454837006964877 : ((((p1 → ((((((p2 ∧ (p3 ∨ p1)) ∨ p3) ∨ p3) ∨ p3) → p1) → p2)) ∨ (True → p3)) ∨ p5) ∨ ((p5 ∧ p1) → (p5 → (p1 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147998893265265706440804792257 : ((((((p4 ∨ p4) ∧ p5) → (((((p4 → p1) ∨ p1) ∧ (p2 ∨ True)) ∨ p5) ∨ True)) → p4) ∨ (p3 → True)) ∨ (((p2 → p5) ∧ p1) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190766397273488280407572241875 : (((((p4 ∨ (p4 → False)) → p4) ∧ p5) ∨ (p5 ∨ p2)) ∨ (True ∨ ((((p4 → p3) ∧ (p3 ∧ p5)) ∨ True) → ((p1 ∧ (p1 → p4)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595651610804511958884730717797 : ((((((p5 ∧ p5) → (((p3 ∧ p1) → (True ∨ (p5 ∧ True))) ∧ p4)) → (((p1 ∧ ((False ∧ p2) → p2)) → p3) ∨ (p2 ∨ False))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207432272758558967662138284691 : (((p1 ∨ (True ∨ (p4 ∧ p3))) ∨ p3) → (((p4 ∧ (((p4 → ((((p5 ∨ False) → p2) ∧ p4) → p4)) → p3) ∧ p5)) → p2) ∨ (True ∨ p1))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44298711369296810425222837551 : ((((p2 ∧ (((p3 ∨ p4) ∨ ((p4 → p1) → ((p2 → p2) ∧ (p4 → p3)))) → p4)) ∧ (p4 ∧ (False → (p2 → (p2 ∧ p2))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117750390699096579979001971804 : ((p4 ∧ ((((p2 ∧ (((p3 ∧ False) → p1) ∧ p5)) ∨ p2) ∨ (p5 → (((p1 → (p3 ∧ (p5 → p4))) ∧ False) ∨ p3))) ∨ p4)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62612458707514225126711754352 : ((p4 ∧ (((p4 ∨ ((((False ∨ p1) ∧ p3) → p1) → ((((p1 ∧ (p2 ∧ False)) ∧ p3) ∧ ((p2 → p4) ∨ p3)) ∨ p5))) ∨ False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259314259363473416299174472340 : ((False → p2) → ((p3 → (p5 ∨ (((True → (((p4 → p4) ∧ (False ∧ (((p3 → True) ∧ p2) ∨ p2))) ∧ False)) ∧ (p3 ∧ p5)) ∨ p3))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181515487713776688354613903432 : ((True → (((((p2 ∧ p2) → p3) ∨ ((p4 ∧ p5) ∨ p2)) ∧ False) ∧ p2)) → (((p3 ∨ (p4 → p5)) → p4) ∨ (((p1 ∧ False) → p1) ∧ False))) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135886304060703809329640397858 : (((p4 ∨ ((((p4 ∨ (False → False)) ∧ p3) → (p2 ∨ p5)) ∨ p5)) ∨ (True ∧ ((p4 → (p3 → p1)) → (True ∨ p2)))) ∨ (p3 ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65202360771390015594624808384 : ((p3 ∨ (((p2 ∨ (((((((p4 ∨ p3) ∧ (p1 ∧ p1)) → p2) ∧ p3) ∧ p4) → p4) ∧ ((p1 ∨ (p2 → p2)) ∧ p3))) ∨ p2) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37930124013708966524834675690 : ((((p1 ∧ ((False ∨ (True ∨ (((p2 ∧ (p1 ∨ (p3 → False))) ∧ (p5 ∨ (False → p3))) ∨ (p2 ∧ p2)))) ∨ p4)) ∧ (p2 ∧ p4)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198316932738496222545026948436 : ((p1 ∧ (p4 ∧ ((p2 ∨ (True ∧ p3)) → p2))) ∨ (((True ∨ ((p3 → p4) ∨ ((p3 → p3) → p5))) → ((p1 → (p5 ∧ p4)) ∧ False)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p3 → p4) ∨ ((p3 → p3) → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617879407003018259770459524883 : ((((((p5 ∨ (False ∧ False)) → (p5 ∧ p2)) → (p3 ∧ (((p2 ∧ ((p5 ∨ ((p5 ∧ p1) ∨ False)) → (p2 ∧ False))) ∧ p2) ∧ True))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345665637732796444047414078877 : (p3 → ((False ∨ (((p3 → ((True ∧ p5) ∧ (((p2 ∧ (True ∧ p4)) ∧ p3) ∨ ((p1 ∨ p2) ∧ True)))) → p1) ∧ (True ∨ (p3 ∨ p5)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206005227301675039889717608383 : ((p1 ∧ (p3 → ((p3 → False) ∧ p5))) ∨ (((False ∨ (p1 ∧ p2)) → ((p1 ∧ (p4 ∧ (False ∧ (True ∧ True)))) ∨ False)) → ((True → False) → p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206149204325399087237182881070 : ((p5 ∧ (((p3 ∧ p4) ∨ p1) ∧ p3)) ∨ ((((p1 → False) ∧ ((p2 ∧ p2) → p5)) ∨ (p3 ∨ p1)) → ((p1 ∧ (p3 ∧ p1)) ∨ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707936510759057451623325082383 : ((((p5 ∧ (p2 → (p5 → ((p1 ∨ p2) ∧ p2)))) ∨ ((p2 ∨ ((((False → p3) ∧ (p1 ∨ p5)) → p3) ∨ True)) ∧ (p1 ∨ (True → True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190515573626039165870005038532 : (((((p2 ∧ ((p2 → p5) → p5)) ∨ p2) → p5) → p3) ∨ ((p2 → ((p2 ∧ (p1 ∨ p3)) ∧ (p4 ∨ p5))) → (True → (True → (p1 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325918412170701770781186808570 : (p5 ∨ (p5 ∨ ((p2 ∧ (p1 ∨ (((p1 → ((p1 ∧ (p5 → (p4 ∧ ((p5 → p3) → p3)))) ∨ p1)) → ((False ∨ p5) ∧ p5)) ∧ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52768227846490233428082927189 : ((((True ∨ (((True → (p1 → False)) ∧ True) ∧ ((p1 ∨ p5) → p1))) → False) → (((p3 ∧ p3) ∨ p1) ∨ (p1 ∨ (True ∧ (p1 ∨ p3))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((True → (p1 → False)) ∧ True) ∧ ((p1 ∨ p5) → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607170584025074463302472997608 : ((((((((p1 ∧ (p4 ∨ p3)) ∧ p1) → p2) ∨ ((p2 ∨ ((p3 ∨ True) ∨ p3)) → ((p5 → (p5 → (False ∧ p3))) ∨ True))) ∧ True) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110910778986285734617460540786 : ((((p4 ∧ ((p4 → ((p2 ∨ ((((p3 → p3) ∧ p4) ∨ p3) → (((p1 ∧ p4) ∨ p2) ∨ p1))) → p1)) ∧ p3)) → p1) ∧ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665901434094212002848644821212 : ((((((False ∨ ((p2 ∧ p5) → ((False ∧ False) → p3))) → (False ∨ ((((p4 → p4) ∨ p4) ∨ False) ∨ p3))) → False) ∧ ((p2 → p5) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2979400942533182503625324532 : ((True → (p5 → p2)) ∨ ((p5 ∨ p1) ∨ (False ∨ (((p4 ∧ p5) → ((False ∨ False) ∧ (False ∧ (((p5 ∧ p5) ∧ True) → p1)))) ∨ True)))) := by
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
theorem thm_5_vars_687596163830768634090544743204 : ((((((p3 ∨ (p2 → (False → ((p4 → p5) ∨ p2)))) ∨ (p1 ∧ (p4 → p3))) → p5) ∧ ((p2 ∨ (p3 → True)) ∧ ((True ∧ p4) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264546971043841980332879739991 : (True ∧ (((p4 ∧ p5) ∨ p2) ∨ ((p1 → (((p5 ∨ ((p1 ∨ (p5 ∧ p5)) → (False ∨ False))) ∨ (p2 ∧ p4)) ∨ (True ∨ True))) ∧ (p4 → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94555836685055691315821441902 : ((p3 ∧ (((p2 → ((p3 ∨ ((p4 ∨ (p4 ∨ (p5 ∨ p5))) ∨ (p3 ∨ p4))) → (((False ∧ False) ∨ p4) ∧ True))) → (p3 ∧ False)) ∧ p4)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → ((p3 ∨ ((p4 ∨ (p4 ∨ (p5 ∨ p5))) ∨ (p3 ∨ p4))) → (((False ∧ False) ∨ p4) ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
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
              exact h5
            case inr h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h21 := h4 h6
  -- We need to get the right conjuct of h21 based on <expert-advice>.
  let h22 := h21.right
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112052985384992438408923449491 : ((((True ∧ p4) ∧ ((p5 ∨ ((((p5 ∧ (p4 ∨ (p4 ∧ True))) ∧ True) ∨ (False → p5)) ∨ p5)) ∧ ((False → False) ∧ p4))) ∨ p1) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357254002145152724138732409035 : (p5 → ((False ∧ p4) ∨ ((((p1 → (False ∨ p1)) → (p2 ∧ p5)) ∨ ((((p1 → p2) → p4) ∧ ((p3 ∧ p5) ∨ p3)) ∨ True)) ∧ (p5 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165710610431753186544211568648 : (((((p5 → True) → p1) → p4) ∧ ((((p1 ∨ p2) ∧ (p2 ∧ (False ∧ p1))) ∧ p4) ∨ p2)) ∨ (((p1 ∨ False) ∨ (p5 ∨ p5)) → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117885144345185660078097959686 : ((p5 ∧ (((p2 ∨ (((True ∧ ((p4 ∧ ((p1 ∧ False) ∨ (p4 ∨ p2))) ∨ (p2 ∨ p4))) ∨ p3) → p2)) ∧ False) ∧ (p3 ∨ p3))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308856199717531568844224043850 : (p2 ∨ ((((p1 → (p5 ∧ False)) → ((p2 ∧ p5) → ((False ∧ (((True ∨ p4) → (True → p5)) ∨ p3)) ∨ ((p4 → p2) ∨ p3)))) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (p5 ∧ False)) → ((p2 ∧ p5) → ((False ∧ (((True ∨ p4) → (True → p5)) ∨ p3)) ∨ ((p4 → p2) ∨ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659992168510980644849182617154 : ((((((((((p4 ∨ p2) ∧ (p3 ∧ p2)) ∧ ((p1 ∨ p1) ∧ p1)) → ((p1 ∨ p4) ∧ (p5 → p4))) ∧ p1) → p2) ∨ p1) → (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



