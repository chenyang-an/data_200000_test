variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114068958404384631509910573553 : (((((p2 ∨ p2) ∨ (False → (p5 ∨ p5))) ∧ ((p5 ∨ ((p2 ∨ False) ∧ False)) ∨ (True → (False → p5)))) ∨ ((p2 → p1) → p4)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115035727791497298502307202797 : (((((False → (p5 → ((p2 ∨ True) → False))) ∧ (p2 ∨ p2)) ∧ p1) ∨ (p2 ∨ (False ∨ ((p1 ∨ (p4 → (p5 ∧ p3))) → True)))) ∨ (False ∧ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1474275705771592782840163801 : (((p1 ∧ ((p2 ∧ p2) ∨ ((((True → False) ∧ (p1 ∨ (((p4 ∧ False) ∧ p4) → p5))) ∨ p2) ∧ (p1 → p2)))) ∨ p4) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785200908942332100370720464351 : (((p4 ∨ ((((p4 ∧ p1) ∧ False) ∨ ((p3 ∨ ((p5 → ((p4 ∨ False) → (True ∨ p3))) ∨ (p1 ∨ (False ∧ p5)))) ∨ (False ∨ p2))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60752105839254917902989109131 : ((True ∧ ((False ∨ (p4 ∨ p1)) → ((p1 → (p5 ∧ ((False ∨ ((True → (p1 ∧ (p5 ∨ p1))) → (False → (p4 ∨ p3)))) → p3))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310513470585449366655825843651 : (p2 ∨ ((p3 ∨ (((p2 → p2) ∧ p4) → False)) ∨ ((p4 → (p3 → (p4 ∧ ((p2 → p1) → ((True ∨ (p3 ∧ (False → p2))) ∧ p4))))) ∨ p2))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337092224931142700615457580165 : (p1 → (((p2 ∨ ((p4 ∧ ((p1 ∧ (False ∧ p1)) ∨ p3)) → False)) ∧ (((False → p2) ∧ (p4 ∨ ((p2 ∨ p4) ∨ p1))) → p3)) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254997896739179601531789301267 : ((p4 ∧ p1) → (((False ∧ (((False ∨ p3) → (p5 ∨ (((p5 ∨ False) → (p4 ∧ ((p1 → (True ∧ True)) ∧ p4))) ∨ p2))) → p3)) ∨ p5) ∨ True)) := by
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
theorem thm_5_vars_49477952222398110335321489085 : (((((p4 ∨ (((p3 ∨ (p3 ∧ (p2 → p5))) ∧ (False ∨ False)) ∧ (((False → p5) ∨ True) ∨ p1))) → p1) → p3) → (p1 ∨ (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342477132083336766476327440646 : (p2 → (((((p3 → (p1 ∧ (p2 ∧ ((True ∧ p4) ∧ p1)))) ∨ True) ∧ p1) → p5) ∨ (True → (p2 ∨ (p2 → (False ∧ (p1 → (p5 ∨ p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356194672132648788776840511561 : (p5 → ((((p4 ∨ ((False → True) ∧ p2)) ∨ True) ∨ ((p4 ∧ (p3 ∨ (p4 ∧ True))) ∧ (True → p1))) → (((p5 ∨ (True ∧ p2)) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40592566096915828966572837984 : (((((p2 ∧ (p4 → ((((p2 → True) ∧ (p4 ∨ (((p5 ∨ (False ∨ p1)) → p4) ∧ (p2 → p3)))) ∨ p2) ∨ p2))) ∧ p5) → p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624004002304054057626050315226 : ((((p2 ∨ (((p1 → p2) ∨ (((p1 ∨ (True ∧ (False ∨ False))) ∧ (True → (((False ∨ True) ∨ p5) → p1))) → False)) ∨ (p4 ∧ False))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_314561372528884896703036576067 : (p3 ∨ ((False ∨ ((p2 ∨ ((p5 → ((p2 ∧ (p3 → False)) ∨ False)) ∨ (True ∧ (p3 → False)))) ∧ True)) ∨ (True ∨ ((p2 ∧ p2) ∨ (p2 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349439664766962691781691679724 : (p3 → (p4 → (p1 ∨ (((p3 ∨ p2) → p1) → (p3 → (False ∨ ((((p1 ∨ (p1 ∧ p3)) ∨ ((p4 → p2) ∧ p5)) → False) → (p1 ∧ p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191790910806906547579311592789 : ((p2 ∨ ((((p1 ∧ (False ∧ p3)) ∧ False) ∧ p2) ∧ p5)) ∨ (((False ∨ (False ∨ False)) → ((p2 ∧ True) ∨ ((p3 ∧ p4) ∧ p1))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136708155499262211706297691771 : (((p2 ∧ False) ∧ ((True → (((p3 → p1) ∧ (((p4 → False) ∨ p1) ∧ ((True → p4) ∨ (p3 ∧ p3)))) ∨ p5)) ∨ p4)) ∨ ((True ∨ p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717875612784664368500069568027 : (((((True ∨ (p4 → p1)) ∧ p4) ∨ (p1 → (p4 ∨ ((((p3 ∧ ((((p2 ∨ (p4 ∧ p1)) → False) → p2) ∨ p2)) ∧ p4) → p4) → p1)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112438357520333446178122939269 : ((((((p3 ∨ False) ∨ (((((p2 ∧ (False ∧ p2)) ∧ (False ∨ p1)) ∧ (p4 ∨ True)) → (p5 ∧ p5)) ∨ p1)) ∨ p1) ∨ p5) → p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62017297105481363279038468693 : ((p2 ∧ (((p1 ∨ p4) ∧ p4) ∨ ((((p2 → (p2 ∧ p1)) ∨ p1) → ((p1 → False) → ((p5 ∨ (p4 ∧ (p5 ∨ p1))) → p3))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68694466454640916594721260918 : ((p4 → ((p1 ∧ (p5 ∧ (p2 ∧ ((p5 → (((p1 → True) → (p4 ∨ p1)) ∧ p2)) ∨ (((p5 ∧ p5) ∨ True) ∨ True))))) ∨ (p2 → p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791749187588802884508221488782 : (((True → ((p3 ∧ (((p5 ∨ (True ∧ ((p3 ∨ ((p2 ∨ (p3 → (p5 ∨ p4))) ∨ p4)) ∨ p2))) → (p5 → p3)) ∧ (False → p1))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166276801522770705547658906560 : ((p4 ∧ ((((p1 ∨ p1) → (p2 → ((False ∨ p2) ∨ ((p1 → p2) ∧ p4)))) → p2) ∧ False)) ∨ ((p4 ∨ p4) → (p3 → ((p1 ∨ True) → True)))) := by
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
theorem thm_5_vars_301631763086918196201687993271 : (False ∨ ((p1 ∨ (False → p4)) → (((p3 ∧ p4) → ((((True ∨ p4) ∨ False) ∧ (p3 → False)) ∨ (p3 → p3))) ∨ (((True ∨ p3) ∧ p5) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160142277342240131435079707635 : ((((((p5 → (p4 → p1)) ∨ p2) ∨ (((p1 ∧ (p5 ∨ p5)) ∧ p2) ∨ p3)) → p4) ∧ (True → p5)) → (((p1 ∧ (p1 ∧ p3)) ∨ True) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164977651835803372836200831212 : (((((p1 → (False ∧ (p3 ∨ ((p3 ∧ True) → p1)))) ∨ (p4 ∧ True)) → (p1 ∧ p1)) → p4) ∨ (((p5 ∧ (p2 ∧ True)) → (p3 ∨ True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135745070891779564779116681043 : ((((p2 ∨ (True → (p2 ∨ False))) ∧ ((p1 ∧ p3) ∨ ((False ∧ p1) → p3))) ∨ (True ∨ ((True ∧ p3) ∧ (p1 ∧ p5)))) ∨ (p2 ∧ (p4 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54227160264224093362454798216 : (((((p2 ∧ p4) ∧ ((p3 ∧ False) → p1)) → p4) ∧ (((p1 → ((p2 ∧ p5) ∧ p2)) ∧ p4) ∨ (((False → p1) ∧ False) → (True → p4)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134002079634642432149552233828 : (((((False ∨ p1) ∨ (((((p4 → p5) → (p4 ∨ ((p4 ∨ False) ∨ p5))) ∧ p2) ∨ p5) ∧ (p3 → False))) ∧ p5) ∨ p2) ∨ (p1 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244098317295938280253789975569 : ((True ∧ p3) ∨ (((True ∨ True) ∧ p3) → ((p5 ∨ False) ∨ (((p4 ∧ p1) ∨ True) ∧ (p3 ∧ (((p3 ∨ (p5 ∧ False)) ∨ (p3 ∧ True)) ∨ p3)))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245829155478105655981226097187 : ((p3 ∧ p4) ∨ ((((True ∧ (((p2 ∧ p5) ∨ p3) ∧ (((p2 ∧ p5) ∨ (True → p2)) → p4))) → False) ∨ (p1 → ((True ∨ p3) ∨ p5))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_33473659471235184771125167472 : ((p4 ∨ ((p1 ∧ (p1 ∧ (p2 → p5))) → (p5 ∨ ((p5 ∨ (True → False)) ∨ ((True → (True → (True ∧ ((p5 ∧ p4) ∧ True)))) → p1))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35986202279508220426166249567 : ((p3 → (((((p5 → (False ∧ p3)) ∧ (p4 ∨ False)) ∨ p5) ∧ True) ∨ (((p1 ∧ (p1 → (p3 → False))) → (False ∨ (p2 → p5))) ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45860388793018568080856106437 : (((p3 → (((((p4 → p5) → p3) ∨ ((p1 → ((p2 ∧ (p2 → p4)) → p3)) → p1)) → ((p4 ∧ p3) ∧ (p3 ∧ False))) ∨ p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247609518479031550257038296557 : ((False ∨ p5) ∨ ((p2 → (p3 ∧ (((p2 ∨ p2) ∨ ((p4 → False) → (p1 → True))) → (p1 ∨ p1)))) ∨ (False ∨ (True ∧ (p1 ∨ (False → p1)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46903205846896748331617615099 : (((((((p5 → (p4 ∧ p5)) ∧ ((False ∧ p2) → ((((p1 ∧ False) ∧ False) ∧ True) → False))) ∨ True) → (p2 ∧ p3)) ∨ False) ∨ (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61601092666119002266154797108 : ((p1 ∧ ((True ∧ (p5 ∧ p1)) → ((True ∨ ((p3 → ((p5 ∧ p5) → ((p2 ∨ (True → (p2 → p5))) → (False ∨ p3)))) → p4)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669814732690801690104235771921 : (((((p5 → (False ∨ (((False ∨ (p4 → p3)) ∧ p1) ∨ ((p5 ∨ p5) ∧ True)))) → (p4 ∧ ((False → p4) ∨ p3))) ∨ ((p1 ∨ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178237884636274613523958070499 : (((p5 → ((p4 ∧ p5) → ((((p5 ∨ p3) → True) ∧ p5) ∨ True))) → False) ∨ ((False ∨ (p3 → p5)) → (((p2 ∨ (p2 ∨ True)) ∨ p3) ∨ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645525495305976943214516500667 : ((((p4 ∨ (False ∨ ((False → ((p5 ∨ (p4 ∧ p1)) → (p4 ∨ (p1 ∨ (True ∧ True))))) → ((True → (p1 ∨ (p2 → p2))) ∧ p1)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300078986209018797368144115244 : (False ∨ ((((False → False) ∨ (((((p2 ∨ p2) ∧ (p5 → True)) ∨ p1) ∨ (p4 ∨ p4)) ∧ (False ∨ ((p4 ∨ p2) → p2)))) → p5) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160139187895388796383251209673 : (((((((p1 → ((True ∧ False) → p5)) ∧ (p2 → (p5 ∧ p4))) ∧ p1) ∨ True) → p4) ∧ (p5 ∨ p3)) → ((False → True) ∧ ((p2 ∨ p4) ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((((p1 → ((True ∧ False) → p5)) ∧ (p2 → (p5 ∧ p4))) ∧ p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149144610934811044804911531140 : (((True ∨ p2) ∧ ((p4 ∨ True) → (((p3 ∨ (False ∧ (p1 ∨ p3))) ∨ p5) ∨ (p2 ∧ ((True → p2) → p2))))) ∨ (p2 → ((p2 ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231378305213782987731784445643 : (((False → p4) ∨ p2) → (((True ∧ p4) → p4) → (p4 ∨ (True ∧ (True ∧ ((p3 ∧ (p4 → ((p1 → p3) ∧ False))) ∨ (p5 ∨ (p5 → True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655666422743922967756572258674 : ((((((((p5 ∧ ((p3 ∧ p5) → False)) → p3) → (False ∨ (p1 → (False ∧ p2)))) ∧ (p5 ∨ True)) ∧ ((False ∧ p5) ∨ p5)) ∨ (p5 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40343341281217160954011682779 : (((((p4 ∧ ((p3 → p4) ∨ ((p5 → (True ∨ (p4 ∨ (p4 ∧ ((p4 ∧ p3) → (True ∧ False)))))) → (p2 → p1)))) ∨ True) ∨ p4) ∨ False) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116583205738905779524287753648 : (((p4 ∨ False) ∧ ((True ∧ ((((p1 ∧ ((p1 → False) ∧ (p1 ∧ (False ∧ p3)))) ∨ p2) → p1) ∧ ((p5 ∧ True) ∧ True))) → p1)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655523871397767089016366974165 : ((((((((True → (p1 ∧ (p3 → p5))) ∧ False) ∨ ((p3 ∨ (p2 ∨ ((p3 ∨ p4) ∨ False))) ∨ False)) → p3) → (False ∨ p1)) ∨ (True ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226209597500625564861580956230 : (((p2 ∨ p2) ∨ p1) ∨ (((((((((p1 ∧ p4) → p5) ∨ (p2 ∧ p4)) ∧ False) → (p5 ∨ True)) ∧ p4) ∧ (False ∧ True)) ∨ True) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679373031739812378109612639154 : ((((p4 → ((((True ∧ (p3 ∧ p4)) → (p1 → p3)) → ((False → True) → (p2 ∨ (p5 ∨ p5)))) ∧ p5)) ∨ (p3 ∨ (p2 ∨ (p1 → True)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192528474234433696959401479295 : (((True ∧ ((True ∨ p3) ∧ ((p3 ∨ p5) ∨ p5))) ∨ p3) → (p4 ∨ (((True ∧ p4) → True) ∧ (False → ((p1 ∨ p3) ∨ ((p2 → p5) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
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
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h24
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h25
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h27
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h28
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h30
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h31
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64140551877656194729636973832 : ((False ∨ ((False ∨ (p3 → p1)) ∧ (((((((False ∧ p3) ∨ ((p4 ∧ p4) ∧ p1)) → (p3 ∧ p1)) ∧ p5) → p3) ∨ p2) ∧ (p3 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322433406990847980902277714021 : (p5 ∨ (((True ∧ ((p4 ∧ p2) ∨ (True → p1))) ∨ (p2 ∧ (p3 ∧ (((True ∨ (((True → False) → True) ∧ (p4 → p1))) ∨ p1) ∧ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330963776402566169902663258243 : (True → (p5 → (((p1 → (False → (((True → p1) ∧ (p5 ∨ ((True ∨ p2) ∨ (((p2 ∧ p4) → p4) ∨ p3)))) → (p1 ∧ False)))) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40915526844401160810101809115 : ((((p3 ∨ ((((True ∧ ((p5 → p4) ∨ p2)) ∧ p5) ∧ (p1 ∨ p5)) ∨ (((True → (True ∨ p3)) ∨ p1) → p5))) ∧ (p5 ∨ p4)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685946725527111591079030469962 : ((((((p5 → (p2 ∨ p2)) ∨ ((p3 ∧ (p5 ∧ False)) ∧ (False ∧ (False ∨ p4)))) ∧ (p1 ∧ p5)) → (True → (((p1 ∨ p3) → p3) ∨ p2))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165246215049231208666446538077 : (((p2 ∨ (True → (p2 → (p5 ∨ (p5 ∧ ((p2 → p3) ∨ (False ∨ False))))))) ∨ (False → p5)) ∨ ((((p4 ∨ (True ∧ True)) ∧ False) ∧ p4) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193198969564941982115121976649 : (((False ∧ (True ∧ (p1 ∧ p3))) → ((p4 ∧ p1) → p3)) → (((p4 ∨ (False ∧ (p1 ∧ ((p2 ∧ p4) ∧ p5)))) ∨ p1) ∨ ((p5 ∧ p3) → p5))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238207161324449776264068111016 : ((True ∨ p4) ∧ ((p4 ∧ (p4 ∨ p2)) ∨ (((p1 ∧ False) ∨ ((p3 ∧ (p1 ∨ ((True ∧ p1) → True))) ∨ (p2 ∨ (False → (p4 ∨ True))))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790483363061500990391437837553 : (((p5 ∨ (False ∨ (((p4 ∧ (((True ∧ (p3 ∧ (p1 ∧ ((((p4 → True) ∨ p1) ∧ p1) ∧ p3)))) ∧ p3) → p5)) ∧ p4) ∧ (p4 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134439626024299961934083689772 : (((((p1 → ((p1 ∧ (((((p3 → p2) ∨ (p4 ∨ p1)) ∧ p4) → False) ∧ (p5 ∧ p4))) ∧ False)) ∧ True) ∧ p1) → False) ∨ ((p4 → p5) → p2)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166144359638583258613762373957 : ((True ∧ (p2 → (((p1 ∨ (p4 ∨ (((p4 → False) ∨ p4) ∨ False))) ∨ (p2 → p1)) ∨ p4))) ∨ ((False → p4) → (p5 → (False ∨ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609243453033684480542443987781 : ((((((p2 ∨ (p2 ∧ p4)) ∨ (False ∨ (((p4 ∨ ((True → ((p1 ∨ p4) → False)) ∧ True)) ∨ ((True ∨ p1) ∨ p4)) ∨ p1))) ∨ True) ∨ p5) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_342897580430923625959188825649 : (p2 → (((p5 ∨ (p2 → True)) ∨ (p3 ∨ True)) → (((p4 ∧ (p5 → (p4 ∧ ((p3 → (True ∧ p3)) → (p3 ∧ (p2 ∧ p4)))))) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172439907198796851446509324511 : ((((p3 ∧ (p1 ∧ p4)) ∧ p5) ∨ ((((p4 ∨ p2) → (p1 ∧ p1)) ∨ p1) → p5)) ∨ (True ∨ ((((False → p2) ∨ (p2 → p4)) ∨ True) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350257960910380457526106561718 : (p4 → ((p1 ∧ (p5 ∨ ((((p1 ∧ p5) ∨ (True ∧ ((p4 → False) ∧ p5))) ∨ (p5 ∧ p4)) → (p3 ∨ ((True ∨ p3) ∨ (p1 ∧ p4)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661408045662257659445887767056 : (((((p4 ∨ ((p4 ∨ ((False → p2) ∨ (p5 ∧ (((((True → p1) ∧ p2) ∨ True) ∧ p4) ∨ p2)))) → p2)) → (p4 → True)) → (p4 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147573052012296582885415375927 : ((((((False ∨ p2) → p4) ∧ (p4 ∨ ((((True ∧ p1) ∧ ((False → False) ∧ p2)) ∧ p5) → p2))) ∧ p5) → False) ∨ (((p2 → False) ∧ False) → p4)) := by
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
theorem thm_5_vars_335713940402627033274813308371 : (p1 → (((p3 ∨ (((p2 ∨ (True ∧ p4)) → ((p5 → p5) → ((((p4 ∧ (p4 ∧ p5)) ∨ p4) ∧ p2) ∧ (p1 ∨ False)))) ∨ p2)) ∨ True) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52672416278703307987939004054 : (((False ∨ ((p1 ∨ p3) → (p2 → (False ∧ (((p2 ∨ p4) ∨ p1) → p3))))) ∨ (False → (((p5 ∨ p4) ∧ True) ∨ (p2 ∧ (True ∨ p1))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15237092007979940701622419631 : (((p3 → ((p1 → (p4 ∧ (p1 ∨ ((p1 ∨ ((False ∨ True) ∨ p3)) ∧ True)))) ∨ (p5 ∧ (p1 ∨ ((p5 ∨ p5) ∧ p5))))) ∨ (p4 → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59314572347246928326158349449 : (((p4 ∨ p1) ∨ (False ∧ (True → (p2 ∧ (p1 ∨ (p3 ∧ ((((p2 ∨ ((p5 → p3) → True)) → ((p5 → p1) ∨ False)) → p1) → p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54122446027640126020230123687 : (((True ∨ (p5 → (p1 ∧ (p5 ∧ ((p5 → p3) → True))))) → (p3 → ((False ∨ ((p3 → (p1 → p5)) → (p5 → p3))) → (p2 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165964009494263640430181592681 : (((False → p5) ∧ (False ∨ ((((p2 ∨ True) → True) → (p2 ∧ (p5 ∧ (True ∧ p3)))) ∨ True))) ∨ (p2 → (((p1 ∧ True) → False) → (p1 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357394356931839322026810795945 : (p5 → ((p4 ∧ p4) → (((p1 ∨ (((((p2 → ((False ∧ (p3 ∨ (p3 → p1))) ∧ (p4 ∧ p5))) ∨ p2) ∨ p5) ∧ p1) ∨ p4)) ∨ p4) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735538576246633763513712467588 : ((((p4 ∨ p5) ∧ (p4 ∧ ((((True ∨ ((p1 → p3) → (p2 → p2))) ∨ (p3 ∧ p3)) ∧ (False → (p5 ∨ True))) → ((p2 ∧ p1) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205252426412089975603066486601 : ((((p1 → p2) ∨ p1) ∨ (p1 ∨ p2)) ∨ ((False ∨ (((p2 ∧ p2) ∧ (False ∧ False)) ∧ (((p4 → p1) ∧ False) → (p3 → (True ∧ p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114022524378007183906686081253 : ((((p1 ∧ (((p5 ∧ (p1 → (((p4 ∨ p5) → True) → True))) → p1) ∧ (p2 ∧ (p1 ∧ p5)))) ∨ True) ∨ (False ∨ (True → p4))) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168851373258322118032207164927 : ((p3 ∨ (p5 ∧ ((p5 → False) ∨ (p5 ∨ ((p3 → ((p5 ∧ (True ∨ p3)) ∧ p3)) → p2))))) → ((((False ∨ False) ∨ True) ∨ True) ∨ (True → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620186160114384940487221026965 : (((((p3 ∧ False) ∨ ((((p3 ∧ False) ∧ (True → (p4 → (((True ∧ p3) ∧ ((p5 → False) ∨ p2)) → (p4 ∨ p5))))) ∨ p2) ∨ False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115712793585150474698115929477 : (((((p3 ∨ (True ∧ p4)) → True) ∨ p1) → (p2 ∧ (((p5 ∧ (p3 ∨ False)) ∧ (p1 → (p5 ∨ (p1 → (p2 ∨ p5))))) ∨ p5))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51731987759436224566508374675 : ((((p5 ∨ (p2 ∨ (p4 ∨ True))) ∨ (False ∨ ((True → p4) ∧ (p3 → (p1 ∧ p1))))) ∧ (((p3 ∧ (p1 → (p3 ∨ False))) ∧ False) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232018919304928053043810071712 : (((p3 ∨ True) → p2) → ((((((p3 ∨ p4) ∧ p3) ∧ ((p3 ∧ (p1 ∧ p4)) → True)) ∨ ((p3 ∧ False) ∨ (True ∨ (p5 ∧ p4)))) ∨ p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_171559004331964978955097676946 : ((((True ∧ ((p4 ∨ (False ∨ (True → p1))) ∨ (p5 ∧ (True → p3)))) → p1) ∨ p2) ∨ ((((False ∧ (p4 ∨ p5)) ∨ True) → (True → False)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (p4 ∨ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40098543097310340129101674608 : (((((p5 → ((p1 → ((((((p4 ∧ False) → (False ∧ (False → p1))) ∨ (p5 → p4)) → p3) ∧ True) ∨ p4)) ∨ p5)) → p5) ∧ False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309805791233023454945693048288 : (p2 ∨ ((((True ∧ p2) → p3) → (((p2 ∨ (((False ∧ p4) ∧ (p1 → True)) → (p3 ∧ p2))) → p1) → p2)) ∨ (((p3 ∧ p5) ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338281649637599785421106131290 : (p1 → (((p2 → p1) → (p3 ∧ (False ∨ p4))) → (p1 ∧ ((((p3 → p4) ∨ p1) ∨ p4) ∧ ((((False ∨ p4) → p1) → True) ∧ (p4 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41900086747850622648888974030 : (((((p4 ∨ p2) ∧ True) → (p2 → (p1 ∨ ((p1 ∨ ((True → (((p5 ∨ p1) ∧ (True → (True ∧ False))) ∨ p2)) ∨ p3)) → p1)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610860724162395875999448313766 : (((((((p4 ∧ (True → p1)) → ((p5 → (p1 → ((p4 ∧ p3) ∨ p2))) ∨ True)) → (p4 → (True ∨ (True ∨ (False → p4))))) → p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344673198693467641744266459159 : (p2 → (p2 → (((p4 → (((p3 ∨ p4) ∧ (False ∧ p2)) → (p3 ∨ False))) → p4) ∨ ((p4 → p3) → ((p4 → (p4 → p1)) ∨ (p5 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797848509376320381661319189013 : (((p1 → ((((True → (p1 ∧ ((((True ∨ p2) → ((p2 ∧ (False → (p1 ∨ p2))) ∧ p3)) → True) ∨ True))) → p2) ∨ True) ∨ (p4 ∧ False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7975151011139467499144888185 : ((((((((False ∨ False) ∧ (p3 → p5)) ∧ p2) ∧ (p1 ∨ (False ∨ (p1 ∧ (p1 → (((p4 ∧ p4) → True) ∨ False)))))) ∨ p1) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_41247255731736027634274528674 : (((((p2 ∨ ((p2 ∧ (True ∧ (False ∨ (p4 ∧ p2)))) ∨ ((p2 ∨ p1) ∨ (p5 ∧ p3)))) ∨ False) ∨ (True ∨ ((p3 ∨ p5) ∧ p2))) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647311327576007240347946472357 : ((((p4 → ((((False ∨ (p5 → False)) ∨ (p4 → (p4 ∧ (p2 ∧ (((True ∧ p2) ∨ True) ∨ p5))))) ∧ (p4 ∧ p1)) ∨ (p2 ∨ False))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117017537237157291424957088749 : (((p1 ∨ p3) → (((((p2 → p2) ∨ (p1 ∧ (((False ∨ ((True ∧ p3) ∨ p1)) ∧ (p2 ∧ False)) ∨ p1))) → p1) → p4) ∨ True)) ∨ (p2 → p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62648423107437012399561171430 : ((p4 ∧ (((p3 → ((True ∧ (((p1 → ((p4 ∨ (True → p4)) ∧ True)) → p1) ∧ (p1 → (p1 ∨ (p5 ∧ False))))) ∨ p3)) ∧ False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49291166406861565204640811756 : (((p5 ∧ (p1 → ((p3 ∧ (((((True ∨ (False ∧ True)) → (True ∧ p5)) ∧ p5) ∧ False) → p4)) → (False ∨ p2)))) ∨ (True → (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346781999206455039000441166118 : (p3 → (((((p5 ∧ (((p2 ∨ p5) → p5) ∧ p5)) ∧ p3) → (p3 → p2)) → ((p1 ∧ (p3 ∨ p3)) ∨ False)) ∨ (((False ∨ p3) ∧ p2) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52923126422099256181820850007 : ((((((p3 → p4) → ((p5 ∧ (p3 → False)) → p1)) ∨ p1) ∧ p1) ∧ (False ∨ ((p1 ∧ p3) ∨ ((p1 ∨ ((False ∧ True) ∨ p1)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136042226126056904940978532185 : (((p3 ∨ ((p5 ∧ ((p2 → (p2 ∨ False)) ∨ p3)) → True)) → ((True ∧ (True → (p1 ∧ p3))) → (p3 ∨ (True → p5)))) ∨ (p5 ∧ (True ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



