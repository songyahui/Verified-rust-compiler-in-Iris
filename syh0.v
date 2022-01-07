From iris.base_logic.lib Require Import gen_inv_heap invariants.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Import lang adequacy proofmode notation.
(* Import lang *again*. This used to break notation. *)
From iris.heap_lang Require Export spawn.
From iris.prelude Require Import options.
From iris.bi.lib Require Import fractional.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import atomic_heap par.

From iris.algebra Require Import lib.excl_auth.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.

From iris.base_logic.lib Require Export invariants. 
From iris.algebra Require Export view frac.
From iris.algebra Require Import proofmode_classes big_op.
From iris.base_logic.lib Require Export own.
From iris.algebra Require Import lib.frac_auth numbers auth.


Set Default Proof Using "All".

Unset Mangle Names.

Section tests.
  Context `{!heapGS Σ, !spawnG Σ} (N : namespace).
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types l : loc.
  Context `{ inG Σ (authR (optionUR (exclR ZO)))} `{OfeDiscrete ZO}.
  Context {A : ucmra}.
Context `{!lockG Σ}.
Context `{!inG Σ (ghostR ZO)}.
Let N1 := nroot.@"bank".

  Definition trans : expr := λ: "x",
  let: "y" := "x" in 
  let: "z" := "y" in
  "x" = "y";; "y" = "z";; #().

Lemma transitivity (x y z l: loc) :
{{{ ⌜x = y⌝ ∗ ⌜y = z⌝ ∗ ⌜x = x⌝ ∗ l ↦ #1 }}} trans #x {{{RET #();  ⌜x = z⌝}}}.

Proof .
iIntros (Φ) "Hxy HΦ".
iRename "Hxy" into "Hx" .
iDestruct "Hx" as "(Hxy & Hyz & Hxx & Hl)".
iDestruct "Hxy" as %Hxy.
iDestruct "Hyz" as %Hyz.
unfold trans.
wp_let.
wp_let.
wp_let.
wp_pures . iModIntro .
iApply "HΦ".
iAssert ( ⌜x = z⌝)%I as %yz.
{
iPureIntro. rewrite Hyz in Hxy. done.
} subst z.
iAssert ( ⌜x = y⌝)%I as %xy. {
iPureIntro . done. } subst y. by iFrame.
Qed.

Definition wp : expr := λ: "l", 
  let: "n" := !"l" in
  "l" <- "n" + #2.

Lemma wp_example (l : loc) (n : Z):
  {{{ l ↦ #1 }}} 
    wp #l 
  {{{RET #(); l ↦ #3}}}.
Proof.
iIntros (Φ) "Hpt HΦ".
wp_pures . wp_load . wp_store . iModIntro .
iApply "HΦ" . by iFrame . Qed .


(*
Definition incr : expr := λ: "l", let: "n" := !"l" in
"l" <- "n" + #1.
Lemma incr_spec (l : loc ) (n : Z) :
{{{ l ↦ #n }}} incr #l {{{RET #(); l ↦ #(n+1)}}}.
Proof .
iIntros (Φ) "Hpt HΦ".
wp_pures . wp_load . wp_let . wp_op .
wp_store . iModIntro . iApply "HΦ" . by iFrame . Qed .
*)

(* COUNTER *)

Definition counter (l : loc) : expr := #l <- !#l + #1.
Definition counter_inv (l : loc) (n : Z) : iProp Σ := 
  (∃ (m : Z), ⌜(n ≤ m)%Z⌝ ∗ l ↦ #m)%I.

Lemma counter_spec (l : loc ) (n : Z) :
{{{ l ↦ #n }}} counter l {{{RET #(); l ↦ #(n+1)}}}.
Proof.
iIntros (Φ) "Hpt HΦ".
wp_pures . unfold counter.  wp_load . wp_op .
wp_store . iModIntro . iApply "HΦ" . by iFrame . Qed .

Lemma x_plus (m:Z) :
  (m ≤ m + 1)%Z.
Proof. 
  Search (_ ≤ Z.succ _)%Z. 
  exact (Z.le_succ_diag_r m).
Qed.

Lemma z_trans (n m: Z) :
  (n ≤ m)%Z -> (n ≤ m + 1)%Z.
Proof.
  intro.
  Search (Z.le_trans)%Z.
  exact (Z.le_trans n m (m+1) H1 (x_plus m)).
Qed.

Lemma parallel_counter_spec (l : loc ) (n : Z) :
{{{ l ↦ #n }}} 
  ((counter l) ||| (counter l)) ;; !#l
{{{ m, RET #m; ⌜(n ≤ m)%Z⌝ }}}.
Proof.
  iIntros (Φ) "Hpt HΦ".
  iMod (inv_alloc N _ (counter_inv l n) with "[Hpt]") as "#HInv".
  - iNext. unfold counter_inv. iExists n. iFrame. eauto.
  - assert (spec_counter := counter_spec l n).
    wp_pures. wp_smart_apply wp_par.
    * unfold counter.
      wp_bind (!#l)%E. 
      iInv N as "H" "Hclose".
      iDestruct "H" as (m) ">[% Hpt]".
      wp_load. 
      iMod("Hclose" with "[Hpt]") as "_".
      + iNext. unfold counter_inv. iExists m. iFrame. 
        iPureIntro. exact H1.
      + iModIntro.  wp_op.
        iInv N as "H" "Hclose".
        iDestruct "H" as (mn) ">[% Hpt]".
        wp_store. iMod("Hclose" with "[Hpt]") as "_".
        -- iNext. unfold counter_inv. iExists ((m+1)%Z). iFrame.
           iPureIntro.
           exact (Z.le_trans n m (m+1) H1 (Z.le_succ_diag_r m)).
        -- iModIntro. admit.
    * unfold counter.
      wp_bind (!#l)%E. 
      iInv N as "H" "Hclose".
      iDestruct "H" as (m) ">[% Hpt]".
      wp_load. 
      iMod("Hclose" with "[Hpt]") as "_".
      + iNext. unfold counter_inv. iExists m. iFrame. eauto.
      + iModIntro.  wp_op.
        iInv N as "H" "Hclose".
        iDestruct "H" as (mn) ">[% Hpt]".
        wp_store. iMod("Hclose" with "[Hpt]") as "_".
        -- iNext. unfold counter_inv. iExists ((m+1)%Z). iFrame.
           iPureIntro.
           exact (Z.le_trans n m (m+1) H1 (Z.le_succ_diag_r m)).
        -- iModIntro. admit.
    * iIntros. iNext.  wp_pures.
      iInv N as "H" "Hclose".
      iDestruct "H" as (m) ">[% Hpt]".
      wp_load. 
      iMod("Hclose" with "[Hpt]") as "_".  
      + iNext. unfold counter_inv. iExists m. iFrame. iPureIntro. exact H1.
      + iModIntro. iApply "HΦ". iPureIntro. exact H1.
Admitted.

(* BANK *)
Definition new_bank: val :=
  λ: <>,
     let: "a_bal" := ref #0 in
     let: "b_bal" := ref #0 in
     let: "lk_a" := newlock #() in
     let: "lk_b" := newlock #() in
    (* the bank is represented as a pair of accounts, each of
    which is a pair of a lock and a pointer to its balance *)
     (("lk_a", "a_bal"), ("lk_b", "b_bal")).

Definition transfer: val :=
  λ: "bank" "amt",
  let: "a" := Fst "bank" in
  let: "b" := Snd "bank" in
  acquire (Fst "a");;
  acquire (Fst "b");;
  Snd "a" <- !(Snd "a") - "amt";;
  Snd "b" <- !(Snd "b") + "amt";;
  release (Fst "b");;
  release (Fst "a");;
  #().

Definition check_consistency: val :=
  λ: "bank",
  let: "a" := Fst "bank" in
  let: "b" := Snd "bank" in
  acquire (Fst "a");;
  acquire (Fst "b");;
  let: "a_bal" := !(Snd "a") in
  let: "b_bal" := !(Snd "b") in
  let: "ok" := "a_bal" + "b_bal" = #0 in
  release (Fst "b");;
  release (Fst "a");;
  "ok".

Definition demo_check_consistency: val :=
  λ: <>,
  let: "bank" := new_bank #() in
  Fork (transfer "bank" #5);;
  check_consistency "bank".


Lemma ghost_var_alloc (a: Z) :
  ⊢ |==> ∃ γ, own γ (●E a) ∗ own γ (◯E a).
Proof.
  iMod (own_alloc (●E a ⋅ ◯E a)) as (γ) "[H1 H2]".
  { apply excl_auth_valid. }
  iModIntro. iExists γ. iFrame.
Qed.

Lemma ghost_var_agree γ (a1 a2: Z) :
  own γ (●E a1) -∗ own γ (◯E a2) -∗ ⌜ a1 = a2 ⌝.
Proof using All.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %<-%excl_auth_agree%leibniz_equiv.
  done.
Qed.

Lemma ghost_var_update {γ} (a1' a1 a2 : Z) :
  own γ (●E a1) -∗ own γ (◯E a2) -∗
    |==> own γ (●E a1') ∗ own γ (◯E a1').
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (●E a1' ⋅ ◯E a1')
          with "Hγ● Hγ◯") as "[$$]".
  { apply excl_auth_update. }
  done.
Qed.


Definition account_inv γ bal_ref : iProp Σ :=
  ∃ (bal: Z), bal_ref ↦ #bal ∗ own γ (◯E bal).


Definition is_account (acct: val) γ : iProp Σ:=
  ∃ (bal_ref: loc) lk,
    ⌜acct = (lk, #bal_ref)%V⌝ ∗
    (* you can ignore this ghost name for the lock *)
    ∃ (γl: gname), is_lock γl lk (account_inv γ bal_ref).

Definition bank_inv (γ: gname * gname) : iProp Σ :=
(* the values in the accounts are arbitrary... *)
∃ (bal1 bal2: Z),
    own γ.1 (●E bal1) ∗
    own γ.2 (●E bal2) ∗
    (* ... except that they add up to 0 *)
    ⌜(bal1 + bal2)%Z = 0⌝.

Definition is_bank (b: val): iProp Σ :=
  ∃ (acct1 acct2: val) (γ: gname*gname),
  ⌜b = (acct1, acct2)%V⌝ ∗
  is_account acct1 γ.1 ∗
  is_account acct2 γ.2 ∗
  inv N1 (bank_inv γ).

Instance is_bank_Persistent b : Persistent (is_bank b).
Proof.
  rewrite / Persistent.
  iIntros "#HQ". iExact "HQ".
  
  Qed.
  (* apply _. Qed. *)


Theorem wp_new_bank :
  (* This is a Hoare triple using Iris's program logic. *)
  {{{ True }}}
    new_bank #()
    (* the `b,` part is a shorthand for `∃ b, ...` in the
    postcondition, and RET b says the function returns b. *)
  {{{ b, RET b; is_bank b }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  unfold new_bank.
  wp_lam.
  wp_alloc a_ref as "Ha".
  wp_alloc b_ref as "Hb".
  iMod (ghost_var_alloc (0: ZO)) as (γ1) "(Hown1&Hγ1)".
  wp_let.
  (* `wp_apply pm_trm`: Apply a lemma whose conclusion is a `WP`, automatically *)
  wp_apply (newlock_spec (account_inv γ1 a_ref)
              with "[Ha Hγ1]").
  - unfold account_inv.
    iExists 0. iFrame. 
  -
  iIntros (lk_a γlk1) "Hlk1".
  wp_pures.
  iMod (ghost_var_alloc (0: ZO)) as (γ2) "(Hown2&Hγ2)".

  wp_apply (newlock_spec (account_inv γ2 b_ref)
              with "[Hb Hγ2]").
    + iExists 0. iFrame.
    + 
  iIntros (lk_b γlk2) "Hlk2".
  iMod (inv_alloc N1 _ (bank_inv (γ1,γ2))
          with "[Hown1 Hown2]") as "Hinv".
      * iNext. unfold bank_inv. iExists 0. iExists 0.
        simpl.
        iFrame. iPureIntro. trivial.
      * wp_let.
  wp_pures.
  iModIntro. 

  
  iApply "HΦ".
  
  unfold is_bank.
  iExists _, _, (γ1,γ2). simpl. iFrame.
  iSplit.
  -- iPureIntro. eauto.
  -- unfold is_account.
  iSplitL "Hlk1".
  ++ iExists a_ref. eauto.
  ++ iExists b_ref. eauto.
Qed.
 
 

Theorem wp_transfer b (amt: Z) :
  {{{ is_bank b }}}
    transfer b #amt
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hb HΦ".
  (* Breaking apart the above definitions is really quite
  painful. I have written better infrastructure for this but it
  isn't upstream in Iris (yet!) *)
  iDestruct "Hb" as (acct1 acct2 γ ->) "(Hacct1&Hacct2&Hinv)".
  iDestruct "Hacct1" as (bal_ref1 lk1 ->) "Hlk".
  iDestruct "Hlk" as (γl1) "Hlk1".
  iDestruct "Hacct2" as (bal_ref2 lk ->) "Hlk".
  iDestruct "Hlk" as (γl2) "Hlk2".
  unfold transfer.
  wp_lam.
  wp_pures.
  wp_apply (acquire_spec with "Hlk1").
  iIntros "(Hlocked1&Haccount1)".
  wp_pures.
  wp_apply (acquire_spec with "Hlk2").
  iIntros "(Hlocked2&Haccount2)".
  iDestruct "Haccount1" as (bal1) "(Hbal1&Hown1)".
  iDestruct "Haccount2" as (bal2) "(Hbal2&Hown2)".
  wp_pures; wp_load; wp_pures; wp_store; wp_pures.
wp_pures; wp_load; wp_pures; wp_store; wp_pures.
rewrite -fupd_wp. (* we need to do this for iInv to work *)
iInv "Hinv" as (bal1' bal2') ">(Hγ1&Hγ2&%)".
iDestruct (ghost_var_agree with "Hγ1 [$]") as %->.
iDestruct (ghost_var_agree with "Hγ2 [$]") as %->.
iMod (ghost_var_update (bal1-amt)
        with "Hγ1 Hown1") as "(Hγ1&Hown1)".
iMod (ghost_var_update (bal2+amt)
        with "Hγ2 Hown2") as "(Hγ2&Hown2)".
iModIntro.
(* we can't just modify ghost state however we want - to
continue, `iInv` added `bank_inv` to our goal to prove,
requiring us to restore the invariant *)
iSplitL "Hγ1 Hγ2".
{ iNext. iExists _, _; iFrame.
  iPureIntro.
  lia. }
iModIntro.
wp_apply (release_spec with "[$Hlk2 $Hlocked2 Hbal2 Hown2]").
  { iExists _; iFrame. }
  iIntros "_".
  wp_pures.
  wp_apply (release_spec with "[$Hlk1 $Hlocked1 Hbal1 Hown1]").
  { iExists _; iFrame. }
  iIntros "_".
  wp_pures.
  by iApply "HΦ".
Qed.

Theorem wp_check_consistency b :
  {{{ is_bank b }}}
     check_consistency b
  {{{ RET #true; True }}}.
Proof.
  (* most of this proof is the same: open everything up and
  acquire the locks, then destruct the lock invariants *)
  iIntros (Φ) "#Hb HΦ".
  iDestruct "Hb" as (acct1 acct2 γ ->) "(Hacct1&Hacct2&Hinv)".
  iDestruct "Hacct1" as (bal_ref1 lk1 ->) "Hlk".
  iDestruct "Hlk" as (γl1) "Hlk1".
  iDestruct "Hacct2" as (bal_ref2 lk ->) "Hlk".
  iDestruct "Hlk" as (γl2) "Hlk2".
  wp_rec.
  wp_pures.
  wp_apply (acquire_spec with "Hlk1").
  iIntros "(Hlocked1&Haccount1)".
  wp_pures.
  wp_apply (acquire_spec with "Hlk2").
  iIntros "(Hlocked2&Haccount2)".
  iDestruct "Haccount1" as (bal1) "(Hbal1&Hown1)".
  iDestruct "Haccount2" as (bal2) "(Hbal2&Hown2)".

  (* the critical section is easy *)
  wp_pures; wp_load.
  wp_pures; wp_load.
  wp_pures.

  (* Now we need to prove something about our return value using
  information derived from the invariant. As before we'll open
  the invariant, but this time we don't need to modify anything,
  just extract a pure fact. *)
  rewrite -fupd_wp.
  (* the [%] here is the pure fact, actually *)
  iInv N1 as (bal1' bal2') ">(Hγ1 & Hγ2 & %)".
  iDestruct (ghost_var_agree with "Hγ1 [$]") as %->.
  iDestruct (ghost_var_agree with "Hγ2 [$]") as %->.
  iModIntro.
  iSplitL "Hγ1 Hγ2".
  { iNext. iExists _, _; iFrame.
    iPureIntro.
    lia. }
  iModIntro.

  wp_apply (release_spec with "[$Hlk2 $Hlocked2 Hbal2 Hown2]").
  { iExists _; iFrame. }
  iIntros "_".
  wp_pures.
  wp_apply (release_spec with "[$Hlk1 $Hlocked1 Hbal1 Hown1]").
  { iExists _; iFrame. }
  iIntros "_".
  wp_pures.
  iModIntro.
  Search (bool_decide_eq_true_2 _ ).
  rewrite bool_decide_eq_true_2. 
  -
  by iApply "HΦ".
  - Search (# _ = # _ ).
Admitted.

Theorem wp_demo_check_consistency :
  {{{ True }}}
    demo_check_consistency #()
  {{{ RET #true; True }}}.
Proof using All.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_apply wp_new_bank.
  *auto.
  (* we use `#Hb` to put the newly created `is_bank` in the
  "persistent context" in the Iris Proof Mode - these are
  persistent facts and thus are available even when we need to
  split to prove a separating conjunction *)
  *iIntros (b) "#Hb".
  wp_pures.
  wp_apply wp_fork.
  - wp_apply (wp_transfer with "Hb").
    auto.
  - (* `check_consistency` always returns true, assuming
    `is_bank` *)
    wp_pures.
    
    wp_apply (wp_check_consistency with "Hb").
    iIntros "_".
    by iApply "HΦ".
Qed.

Theorem wp_fork_alt (P Q: iProp Σ ) (e e': expr) :
  (P -∗ WP e {{ λ _, True }}) -∗
  ∀ (Φ: val → iProp Σ), (Q -∗ WP e' {{ Φ }}) -∗
  (P ∗ Q -∗ WP Fork e;; e' {{ Φ }}).
Proof.
  iIntros "Hwp1" (Φ) "Hwp2 (HP&HQ)".
    (* the details of the rest of this proof aren't important *)
    wp_apply (wp_fork with "(Hwp1 HP)").
    wp_pures.
    wp_apply ("Hwp2" with "HQ").
Qed.

