variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313334192703434757547345838760 : (p3 ∨ ((p5 ∨ ((False ∨ p4) ∨ ((p4 ∨ (p3 ∧ (p5 ∨ ((False ∨ p2) ∧ ((p4 ∧ p2) ∧ (((True ∨ p3) → p4) → p5)))))) ∨ True))) ∨ False)) := by
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
theorem thm_5_vars_684430411814022110003533920853 : (((((((False ∨ ((p3 ∨ p2) ∨ p5)) ∨ p2) ∨ p4) ∨ (((p1 ∧ (p5 → p1)) ∧ False) → p3)) ∨ (p3 → (p1 ∧ ((p1 ∨ p3) ∧ p1)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135378559686544301832312691544 : ((((p2 ∧ (p1 → (((p3 ∨ (p2 ∨ ((False ∨ p5) → True))) ∧ (True → p5)) ∧ p3))) ∨ p2) ∨ (True ∨ (p4 ∨ p2))) ∨ (p2 → (p3 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231188352127148953064606504349 : (((p2 ∨ p5) ∨ p4) → ((p3 ∧ ((((((p1 ∨ p3) ∧ (p1 ∧ (p4 ∨ (False → p4)))) → p2) → p3) → p1) ∧ ((p4 → p3) → p5))) ∨ True)) := by
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
theorem thm_5_vars_61617371975370174642788381643 : ((p1 ∧ ((p3 ∧ False) ∨ ((p1 → (((p3 → True) ∧ ((False ∨ (p4 ∨ ((((p4 → p5) → p1) ∨ p3) → p2))) → False)) → p2)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150310455574487429335167048650 : ((p4 → ((False ∨ p3) ∨ ((p5 ∧ (p2 ∧ (((((p4 → p3) → True) → True) ∧ p4) → (p4 ∧ p4)))) ∨ p2))) ∨ (p5 ∨ (p1 → (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722314708216100836583293189090 : (((((p1 ∧ p4) ∧ False) ∧ ((p5 ∨ p5) ∧ (((p4 ∨ False) ∨ (p4 ∨ (((p5 → True) ∧ ((p1 → p3) → p3)) → p2))) → (False → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444144514207600423309603629678 : (((((True → p5) → ((p3 ∨ (((((p5 ∧ True) → ((True ∨ p2) ∧ True)) → p2) ∨ p2) ∧ p4)) ∧ (False → p2))) ∨ ((True ∨ p3) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57845454613317380224560572516 : (((p5 ∧ (p5 → False)) → (((((False → ((p1 ∧ p2) ∧ True)) → (p3 ∧ ((False ∧ p5) ∧ (p2 ∨ True)))) → True) → (p1 ∨ False)) ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810733122477242045974458531812 : (((p5 → (((p2 → p1) → True) → (p5 → ((((False ∧ (((False ∧ p2) ∨ ((p4 → p4) ∧ p5)) → True)) ∨ (False → p4)) → p4) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114942110814306640885018046071 : (((((p4 ∧ False) → True) ∨ (p4 → ((p1 → (p1 ∨ False)) → (p5 → True)))) → ((False → True) ∧ ((True ∧ p1) → (p3 ∧ False)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38654622200400449174008557340 : (((((p3 ∧ p1) ∨ ((p2 ∧ (p4 ∧ p4)) ∨ p2)) → ((p1 ∨ (False ∨ p5)) ∧ (True ∧ (False ∨ ((p4 → (p3 ∨ p1)) ∨ p4))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43406896141453700786432837104 : (((((p1 ∧ (((p5 ∨ False) ∨ False) ∨ ((p1 ∨ (False ∧ p4)) ∧ p4))) → (p4 ∧ (p3 → (((p4 → True) → False) ∨ p5)))) ∨ p1) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732972587133537592982611300046 : ((((p2 ∧ p3) ∧ (((p4 ∨ p5) → p5) ∧ (((p4 → (((p4 ∨ False) → p3) ∧ p5)) ∧ p5) → (p4 ∨ (((p5 → p4) → p1) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314440086702955939390161801612 : (p3 ∨ ((p2 ∨ (False ∨ (((p3 ∧ True) → (p2 ∧ (((p1 → p3) ∧ p3) ∧ p4))) → ((p1 ∨ p3) ∧ False)))) ∨ (True → ((p4 ∧ True) → True)))) := by
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
theorem thm_5_vars_786754442388289826056568018973 : (((p4 ∨ ((p1 → (p3 ∧ (True ∧ p5))) ∧ (((((p4 → False) ∨ (False ∨ (p4 ∨ ((p1 ∨ p3) → p5)))) → p4) → (p3 → p2)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118835057049754662517332988698 : ((True → ((p2 ∧ ((p1 → (p4 → (True ∧ (False ∧ ((p2 ∧ (p3 ∧ True)) → (False ∧ p4)))))) ∨ (p1 ∧ p5))) ∨ (p1 → p1))) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214824296183477227707368985306 : (((p4 ∨ p1) ∨ (True → p5)) ∨ (((p1 → p4) ∨ p3) → ((p2 ∨ p2) ∨ ((p1 ∨ p2) → (False → (((p4 → p4) → p1) ∧ (p2 → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h9
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146959144707323930611593623909 : ((((p3 ∨ ((p1 ∨ p1) ∨ (p5 ∨ ((p5 ∨ (p5 → (((p5 ∨ True) ∧ True) ∧ p4))) → p2)))) ∨ True) ∧ True) ∨ (((p2 ∨ p4) → True) ∧ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40234521836332023593348761885 : ((((p2 ∧ (p1 → ((p4 → (((p3 ∨ (False → (False ∨ (p2 ∨ False)))) ∨ True) ∧ ((True ∧ (p3 → p4)) ∨ p1))) → p2))) ∧ p5) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695603059756568973611589228724 : ((((((True → (p1 ∨ p2)) ∨ (p1 ∧ p5)) ∧ (p3 → (False ∨ (False ∧ p2)))) → (p5 ∨ (p4 ∨ (((p4 → p3) ∧ (False ∨ p2)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702396578247751869127958797499 : (((((((p3 ∧ p3) ∧ p5) ∧ ((True ∨ p2) → True)) ∨ p3) ∨ ((p1 ∧ ((p1 ∧ ((False ∧ p2) ∨ False)) ∨ p1)) ∨ (p2 → (True → p2)))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112072157652157767095537660001 : ((((p4 → False) ∧ ((p2 ∨ p4) ∧ (((((p4 ∧ (p4 → (p1 ∨ False))) ∨ p5) → p2) ∧ p5) ∨ ((True ∨ p2) ∨ False)))) ∨ p3) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150050202932983797412655976739 : ((True → (((((False → (True ∧ p4)) ∨ p5) ∧ (p4 ∧ ((((p1 → False) ∨ p2) → True) ∧ p5))) ∧ False) ∨ False)) ∨ (p5 ∨ (p5 ∨ (p1 → p1)))) := by
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
theorem thm_5_vars_677606962255571215054420903873 : ((((((((p5 ∧ p2) ∧ (((((p1 → True) ∧ p4) ∧ p4) → (p2 ∨ p5)) → p5)) → p5) ∨ True) → p3) ∨ (p5 → (False ∨ (p5 ∨ p4)))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60413165959670978303637780573 : (((p4 → p1) → ((((p3 ∧ (True ∧ p5)) → ((p5 ∨ (False → (((p4 ∧ p1) → p4) → (p4 ∨ True)))) → (p3 ∧ p1))) → p3) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4027276548947312729895042195 : (p2 ∨ ((p5 ∨ (p3 ∨ ((p5 ∧ p1) ∨ (p4 ∧ ((p2 ∨ (p3 ∧ (p5 → p4))) ∨ (p5 ∨ ((True ∨ (False ∧ p4)) ∧ p4))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69075603136621364894975116550 : ((p5 → (((((p5 → ((True ∨ ((p4 ∧ ((p5 ∨ p4) → p1)) ∧ (True ∧ p3))) ∧ p4)) ∧ p1) ∧ True) ∨ (p4 ∧ (False ∨ p3))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62071430106883688172756238255 : ((p2 ∧ (False ∧ (((False → True) → False) ∨ ((((p5 ∨ (True → ((p5 → p4) ∨ p1))) ∧ p2) ∧ (p1 ∧ (p1 → p4))) ∨ (p3 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320292323604781960412473521861 : (p4 ∨ ((p4 ∧ p4) ∨ ((p4 ∧ (((p1 ∧ False) ∧ p4) → False)) ∨ ((((p2 ∨ p2) ∨ (((p2 ∧ p4) → p1) → True)) → (p4 ∨ p1)) ∨ True)))) := by
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
theorem thm_5_vars_42135231923592003723020742941 : ((((p3 ∨ p1) → ((p3 ∧ ((False → ((((((p2 ∨ True) ∧ p3) ∧ (p5 ∧ (p2 ∨ p2))) → True) → p1) ∨ p1)) → False)) ∨ p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346902481404063001017649444354 : (p3 → (((True → ((False ∧ p5) → ((p1 ∧ p5) → (((p3 ∧ p2) ∧ (p5 → True)) → p1)))) → p1) ∨ ((((p4 ∨ p3) → p2) ∨ p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102612125468419234024994483805 : (((((((True ∨ p1) ∨ ((p5 → (p4 → (p2 → (p2 → p4)))) → (False ∨ (p3 ∧ p1)))) ∨ (p3 → p2)) → p4) ∧ p2) ∨ True) ∧ (False ∨ True)) := by
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
theorem thm_5_vars_105441541603576637289281498366 : (((((p1 ∨ ((((False ∨ (p2 ∧ True)) → p4) ∨ p3) → False)) → ((p3 ∨ False) ∨ p4)) ∨ p2) ∨ ((True ∧ p4) ∨ (True ∨ p3))) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_192311688212689460890710295647 : (((p2 ∧ (((True ∨ p4) ∧ p4) ∨ (p5 → False))) ∧ p4) → (False ∨ ((((p2 → True) ∨ p3) ∧ (p3 ∨ (p2 ∨ False))) ∨ ((p3 ∨ p2) ∧ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320336421000830966097226442474 : (p4 ∨ ((p5 ∨ p3) ∨ ((((p1 ∨ p4) → (False → ((p3 → True) → ((p4 → p1) ∨ p5)))) ∧ p1) ∨ (p3 → (p1 ∨ ((False → p5) ∧ p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160301897145095572559697464250 : ((((((True ∧ p4) ∧ (((p4 → p1) ∧ True) ∨ (p3 ∨ False))) ∧ p4) → (p2 ∧ False)) → (False ∨ p1)) → ((False ∧ (p1 ∨ True)) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610049777213291646815008520956 : (((((((((False ∧ p4) ∧ p2) → (p3 ∨ (((p5 → p2) ∧ True) ∧ (p1 ∨ p2)))) ∨ (((False → p2) ∨ p4) → p2)) ∧ True) → p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_249313760272269635295192265269 : ((p4 ∨ p5) ∨ ((((p2 ∨ (p3 ∧ p2)) ∧ False) ∨ (True ∨ (p1 ∧ p3))) ∨ (((True ∧ (False ∧ (True → (True → p1)))) ∧ True) ∨ (p3 ∧ p3)))) := by
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
theorem thm_5_vars_45226460448562986463292041305 : (((p1 ∧ ((((((p1 ∧ ((p1 ∧ p2) ∧ p1)) ∨ ((p4 ∧ (True ∧ p5)) ∧ p5)) ∨ (p5 ∨ p4)) ∨ p1) ∨ (p1 ∨ p3)) ∧ p2)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39878756537110294649667078950 : (((p2 → (((p3 ∧ p3) ∨ ((((p4 ∨ p1) ∨ ((False ∧ p4) → ((p5 ∧ False) → p5))) ∧ True) ∨ p2)) ∧ ((p5 ∨ p3) → False))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616567627066863991739533588443 : ((((((((p1 ∨ p4) ∧ (p2 → p5)) ∨ (p3 → p3)) → True) ∧ (p5 → (p1 → (((p5 ∨ p1) ∧ True) → ((p5 ∧ p3) → False))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_606612546934382313588938418583 : ((((((p2 ∧ ((p4 → (p4 ∨ ((p1 → p1) → (p2 ∧ ((p5 → (False → (p2 → p5))) → p4))))) → (p5 ∨ p2))) → p4) ∧ p4) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_306221564983847518275532451617 : (p1 ∨ (((True ∨ p5) ∨ p1) → (((p1 ∨ ((p4 → ((False ∧ p3) ∨ p4)) → p4)) ∨ p1) → ((p5 ∨ (True ∨ p3)) ∨ ((p1 ∨ p1) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      cases h1
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597684216354760791345610974705 : ((((((p2 ∨ p3) ∨ (p2 ∧ True)) → (False ∨ ((True ∧ (p1 ∧ (True → (((p3 ∧ True) ∨ False) ∨ (p1 ∨ p3))))) → (p5 ∧ p2)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184481757190733099712315254666 : ((((((p4 ∧ True) ∧ (False ∨ p5)) → p5) → p4) ∨ (False ∨ p4)) ∨ ((p1 ∨ (True ∧ True)) → ((p4 → (((False ∧ p3) ∨ p4) ∧ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248169868000577364696628811555 : ((p2 ∨ False) ∨ ((p2 ∧ p1) ∨ ((((((p5 → (p3 ∨ p3)) ∨ ((True → ((p4 → p1) → p3)) → False)) ∧ (p4 ∧ True)) ∨ True) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227698122529951690456895585522 : ((p1 ∧ (p1 ∧ True)) ∨ (((p2 ∨ (((p1 → p2) ∨ ((p1 ∧ (p3 → p3)) ∧ (p3 → p3))) → (p5 ∨ p5))) → (p3 → False)) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3166016056333566718275015876 : ((p4 → p4) ∧ ((p5 → (((p5 → ((p3 ∨ ((p5 → (p3 ∨ True)) → (False ∧ (p4 ∧ p4)))) ∨ True)) ∨ (p1 ∨ p1)) ∨ p5)) ∨ True)) := by
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
theorem thm_5_vars_799581693533351002012385277876 : (((p1 → (p4 ∨ (((p3 → False) ∧ p1) → (((False → (((p4 ∨ (p1 ∧ False)) ∧ (True ∧ p1)) ∨ p2)) ∧ (p1 → p5)) ∨ (p2 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685574281525492287320917130270 : (((((((p4 → False) ∨ (p5 ∧ (((p3 ∧ (False → (True → p4))) ∨ True) ∨ p3))) ∧ p4) ∨ p3) → (((p4 ∧ False) ∨ (False → p2)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53769112343641337415341023546 : ((((((p5 → ((p4 ∨ p4) ∧ p5)) ∨ p2) ∨ p4) ∨ p3) ∨ (p2 ∨ (((p4 ∧ ((True → (p4 ∨ True)) ∨ p3)) → p5) ∧ (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202533670283495670870886866255 : (((True ∧ (p5 ∨ True)) ∨ (True ∧ p2)) ∧ ((((((p2 ∧ p3) ∧ True) ∨ (p4 → (((p3 ∧ p3) ∨ False) ∨ p5))) ∧ False) ∧ (True ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133284057661195715365338078277 : ((p2 → (((p5 → p4) ∧ (p5 → True)) → (((((p5 ∧ ((p4 ∨ (p5 ∨ p4)) ∨ p3)) → p2) → True) → p1) ∨ True))) ∧ (True → (True ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136508743624037861199806246338 : (((p3 ∧ (False ∧ True)) ∧ ((p2 ∧ ((False → p5) ∧ p3)) → (p1 ∧ (True ∧ ((p3 ∧ ((p1 ∧ False) ∨ True)) → p5))))) ∨ (p3 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762122404071780140664074584183 : (((p3 ∧ ((p5 ∨ (((p5 ∨ (True → p1)) ∨ (p3 ∨ False)) ∧ (p2 ∧ ((False ∧ p4) ∨ ((False ∨ (p5 ∧ False)) ∨ p4))))) ∧ (p5 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165245059552728555099137749255 : (((p1 ∨ (True ∧ ((p3 ∨ p3) ∧ (((p2 ∧ p4) ∧ (p1 ∨ p5)) ∧ False)))) ∨ (p2 ∨ p2)) ∨ ((True → p2) → (False → ((False ∨ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789652982186522768439955073804 : (((p5 ∨ (((True ∧ ((p2 → True) ∧ p2)) ∧ p5) ∨ (False ∨ ((False ∨ p3) → (((((p4 ∧ p3) → True) ∧ p3) ∧ (True ∨ True)) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322202700999295227487656945098 : (p5 ∨ ((((True ∧ (False ∨ ((p4 → (True ∨ p3)) ∧ ((p1 ∧ (((p2 → (p2 ∨ p3)) ∨ True) ∧ (False → p1))) ∨ p1)))) ∨ p3) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710455947746542795990729534991 : (((((False ∧ (p3 ∨ (p5 ∧ p5))) → p5) ∧ (p2 ∨ (p4 ∨ (((p5 ∨ p3) ∨ (p3 ∧ True)) ∨ ((True ∧ (True ∨ (False ∧ p2))) ∨ p5))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_314552653977668102710886721935 : (p3 ∨ (((True → (p2 ∨ True)) ∧ (((p5 ∨ (p3 ∧ (False → True))) ∨ p4) → ((p1 ∨ p5) ∧ False))) ∨ (p5 → (True ∨ (p3 → (True ∧ False)))))) := by
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
theorem thm_5_vars_588064433310587660225886013556 : (((((((p5 ∨ (False → (((p5 ∧ p5) ∨ p1) → False))) → (p2 ∨ (False ∨ True))) ∧ (((p4 → p4) → (False ∧ p4)) ∧ True)) ∨ p2) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60531953507154771651538511549 : ((True ∧ ((((False ∨ (p1 → (p3 ∧ (p3 → p5)))) ∧ (p2 → (p1 ∧ (((p5 → (p1 ∧ p5)) ∨ p2) ∨ p5)))) ∨ (p1 ∨ p1)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233761312990069343281277118703 : ((p3 ∨ (p1 ∨ p1)) → ((((p5 ∨ (True → p1)) ∧ (p5 → False)) ∨ ((p1 ∧ (p3 ∨ (((False ∨ False) → p4) ∨ True))) → (True ∧ True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691898692297790603375592229800 : ((((p1 → (p2 → ((p2 ∧ (True ∧ False)) ∨ (p4 ∨ ((p5 → (p5 → False)) ∨ p1))))) → (p5 ∨ ((p5 → p1) → ((p1 → p3) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184230801851476489582451791515 : ((((p1 → (((p3 → (p5 ∨ p3)) → p2) → p2)) ∨ p5) → False) ∨ (((p2 → p4) ∨ ((p3 → (p4 ∧ False)) → True)) ∨ (p2 ∨ (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205688706498873370995865294390 : (((p5 ∨ False) ∨ (p4 → (p1 → p5))) ∨ (((p3 → (False → p1)) → p4) ∨ (((p3 → p2) ∨ p3) ∨ (p4 → (True ∨ (p3 ∧ (True → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_171710465574212992205405501778 : (((p5 → ((((False ∧ p4) → (True ∧ (True ∧ p2))) ∧ p5) → (p3 ∧ p4))) ∨ False) ∨ ((((False ∨ True) → (p2 ∧ False)) ∧ p3) → (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47741054103983272263488108866 : ((((((True ∧ (p2 → (False ∨ p1))) ∨ (p4 ∨ (p2 → False))) ∨ ((True ∨ False) ∨ ((p1 → p4) → (True → p1)))) ∨ False) → (False ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137749112820302430935894760135 : ((p2 ∨ (((((p1 ∨ ((p5 ∨ ((p3 → p5) → p2)) ∧ p2)) ∨ (p5 → (p5 ∨ (p2 → p2)))) → p2) ∨ p1) ∨ True)) ∨ ((p2 → False) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55493123726584201778493723782 : (((((p3 → p5) → p4) → (p3 → True)) → (p5 → ((False ∨ (((((p4 → (p5 → False)) → p3) ∧ p5) ∧ p1) → p3)) ∨ (p3 ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257814309870805478046889133914 : ((p3 ∨ p5) → ((True ∧ (p2 ∨ (((True ∧ ((p4 ∨ True) ∨ False)) → p3) → True))) ∧ ((p4 → ((p1 → (p4 ∧ p3)) → p2)) ∨ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635260250666351637972916113416 : (((((p4 → ((((False ∨ p1) → (p3 ∧ (p4 ∧ p5))) → ((p2 ∨ p2) ∨ (True ∨ (p2 → False)))) → False)) → ((p5 ∨ True) → p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204554164335110024517078604657 : ((((False → (p4 → p3)) → p1) ∨ p2) ∨ (((p5 ∧ ((((p2 ∧ (((p5 ∧ p1) → False) → False)) ∨ p3) ∧ (p1 → p2)) → False)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258813806058450639454635141877 : ((True → False) → (p1 → ((False → (p3 ∨ p3)) ∧ (p4 ∨ (((p1 ∧ ((((((p5 ∨ False) → p4) ∧ False) ∧ p1) → p4) → False)) → p4) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_207135501815284034466916335528 : (((True → (False ∧ (False ∨ True))) ∧ p4) → ((p1 ∧ ((((((p1 ∨ (p1 ∧ p5)) → p1) ∧ p2) → False) ∧ (p2 ∨ False)) ∧ (p2 ∧ p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356036907311605228836106348278 : (p5 → (((p1 ∧ p1) ∧ ((p1 ∧ ((p4 → ((p4 → False) → (p1 ∧ (p2 ∨ (p1 → True))))) ∧ False)) ∨ p1)) ∨ (p2 ∨ (p1 ∨ (p5 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116311259300000418830312565583 : (((p3 → (p1 → p2)) ∨ (((p4 → p1) ∨ p2) ∨ (p2 ∨ ((p1 → p1) → (p2 ∨ ((((p2 → p2) ∧ p2) ∨ False) ∨ p3)))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200932419041567127621234888357 : ((p1 ∨ (p2 ∧ (p5 → ((p1 ∧ p5) ∨ False)))) → ((p5 ∨ (p1 ∨ p1)) → (((p5 → p1) ∨ p1) ∧ (((True ∨ p2) → (p2 ∧ p3)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
  -- Implications on the right can always be decomposed.
  intro h25
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h27 =>
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h28 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h29 := h25 h28
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h34 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h35 := h25 h34
      -- We need to get the right conjuct of h35 based on <expert-advice>.
      let h36 := h35.right
      -- One of the premise coincides with the conclusion.
      exact h36
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h39 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h40 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h41 := h25 h40
        -- We need to get the right conjuct of h41 based on <expert-advice>.
        let h42 := h41.right
        -- One of the premise coincides with the conclusion.
        exact h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h46 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h47 := h25 h46
        -- We need to get the right conjuct of h47 based on <expert-advice>.
        let h48 := h47.right
        -- One of the premise coincides with the conclusion.
        exact h48
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h50 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h51 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h52 := h25 h51
        -- We need to get the right conjuct of h52 based on <expert-advice>.
        let h53 := h52.right
        -- One of the premise coincides with the conclusion.
        exact h53
      case inr h54 =>
        -- Conjunctions on the left can always be decomposed.
        let h55 := h54.left
        let h56 := h54.right
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h57 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h58 := h25 h57
        -- We need to get the right conjuct of h58 based on <expert-advice>.
        let h59 := h58.right
        -- One of the premise coincides with the conclusion.
        exact h59



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114905364672617119793267857782 : (((((((True ∧ p4) → True) ∨ (p2 ∧ ((p5 ∧ p1) → p5))) → p4) ∧ p4) → ((False → False) ∧ (((False ∧ p3) ∨ p5) ∧ p4))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754280479735544031988972405053 : (((False ∧ ((p2 → p1) ∧ ((((((((p4 → (True ∧ p1)) → (True ∧ ((p5 → p1) ∨ p5))) → p5) ∧ p5) ∨ True) ∧ p3) → p1) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134325542565875602256177914989 : (((p2 ∧ ((p5 ∧ (p1 ∧ ((((p4 → (p3 ∨ p4)) → p4) ∧ (p5 → p4)) → (p2 ∧ True)))) ∧ (p2 → p5))) ∨ p4) ∨ (p4 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138143647239932756861593701252 : ((p1 → ((p2 ∧ ((((p4 ∨ ((p3 → (((p3 → p2) → p3) ∨ p2)) → False)) ∨ p2) ∧ False) ∨ (False ∧ p1))) ∧ p3)) ∨ (False → (True → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256567692358805211048047883160 : ((False ∨ p5) → (p2 → ((p5 ∨ True) → ((p4 ∧ (p5 ∧ (((p1 ∨ (p4 ∨ p1)) → ((False ∧ (p4 ∧ False)) ∨ p4)) ∧ True))) ∨ (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48925365161359213253666987103 : ((((((p2 → ((False → p2) ∧ ((False ∧ (p4 ∧ (False → (p3 ∨ (p1 → p1))))) ∨ False))) → p3) → p1) ∧ p3) ∨ (p2 ∧ (False → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193922751224640131911311336923 : ((p1 ∨ (True ∧ (p2 ∨ (((False → True) → True) ∨ p4)))) → (((p2 ∨ (p1 ∧ (p3 ∧ True))) ∨ (p4 ∨ True)) ∨ (((p1 ∨ False) ∧ False) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40956267335647221826708434232 : ((((((((p1 ∧ False) ∧ (True ∨ p3)) ∨ (p5 ∨ ((p5 → True) → p1))) ∨ (p2 → True)) → (False ∧ (False ∧ p3))) ∨ (p5 → p2)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234883562135091256166243286293 : ((p5 → (p4 → p5)) → ((((((p4 → p5) → ((p1 ∧ p2) ∧ ((p3 ∨ (p1 ∧ False)) → (p4 → (p3 → p3))))) ∨ p1) ∨ p2) ∧ p1) → p1)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247502590133350773961540568103 : ((False ∨ p3) ∨ ((p5 ∨ p1) ∨ (((((p4 → ((p5 ∨ ((p4 ∨ p4) → (p2 → p4))) → (p5 ∧ p2))) ∨ p1) ∨ (p3 ∨ True)) ∨ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656682007139311988370369856785 : (((((((p1 ∨ p3) ∧ False) ∧ (p3 ∨ p4)) ∧ (False → ((((p5 → p5) ∧ (p1 ∨ True)) ∨ ((p2 ∨ p1) ∧ False)) ∨ True))) ∨ (p2 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178897307695073196354308190549 : (((p1 ∨ p2) ∧ (((False ∨ (True → p5)) ∨ ((p3 → True) ∨ True)) ∧ p4)) ∨ ((((p5 → p5) → p4) → (p1 → p3)) ∨ (True ∨ (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210532203632058420288338166540 : ((((p1 ∧ p4) ∧ p5) → p5) ∧ (((((((True ∨ True) → p3) ∨ ((p5 ∧ p4) → (p3 → p5))) → False) ∧ (False → p2)) ∨ p3) ∨ (True ∨ p3))) := by
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
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592685715705414227568747525065 : (((((p5 → ((((p2 ∨ ((p4 ∨ p1) ∧ False)) ∨ (False → p2)) → (p2 ∧ ((p4 ∧ (p2 → p2)) ∧ p2))) → p5)) → (p5 ∧ p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767863208677551422605479070586 : (((p5 ∧ (((p3 ∨ (((p3 → p5) → (p3 → ((p4 ∧ p4) ∧ p4))) ∧ p3)) → (((True → p1) ∨ (False → False)) → (p2 → True))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186292124470106310328202159735 : (((((p2 ∧ (False ∧ p1)) → ((p5 ∨ p3) ∧ p3)) → p3) → p2) → (((p2 → ((((p5 ∨ p2) ∧ p3) ∧ False) ∨ p3)) ∧ (True ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147421964454632223803943357150 : ((((p5 ∧ (True ∧ p5)) ∧ ((((((p2 ∧ p1) → True) ∨ (p3 ∨ p2)) → (True ∨ p1)) → p1) ∧ p5)) ∨ p5) ∨ ((p5 → True) ∨ (p3 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55986346899398303972103894045 : ((((p5 ∧ (p3 → False)) ∧ True) ∨ (((False ∨ True) → ((False ∨ p1) → p2)) → ((p1 ∨ False) ∧ (((p2 → (False ∨ p3)) ∨ p4) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636207916011745753865108910242 : ((((((False ∧ p3) ∧ ((True ∨ ((p1 ∧ True) → p3)) ∨ (True ∧ ((True ∧ p3) → False)))) ∨ ((p3 ∧ p5) → (False ∧ (p5 → p4)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207954895179551333872743593330 : (((p4 → (p1 ∧ p5)) ∧ (p3 ∧ True)) → ((((p1 ∨ (p2 → True)) ∧ ((p2 → p2) → (p2 ∧ p5))) ∧ ((p4 ∧ p1) → False)) ∨ (p3 ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136418604380281401635758746602 : (((((p1 ∧ p1) ∨ True) ∨ True) → (((p5 ∨ p5) ∧ (p3 ∧ False)) ∨ ((False ∧ (p3 ∨ p1)) → ((True ∨ False) → p5)))) ∨ (True ∧ (p2 ∨ p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h6.left
        let h10 := h6.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h13.left
        let h17 := h13.right
        -- False on the left can always be used.
        apply False.elim h16
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h20.left
      let h24 := h20.right
      -- False on the left can always be used.
      apply False.elim h23
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



