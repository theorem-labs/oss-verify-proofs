(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep Relim LB_Logic LB_Kernel.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Unforced.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section WithCeiling. Context {CE__ : Ceiling}.

Lemma vis_flat_L {A} B n (k : resp -> itree node (exc A)) mo (Q : A -> Model -> Prop) (R : A -> Model -> Prop) :
  (forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end) ->
  node_noerr n mo ->   (* [comment removed for export] *)
  etwf (Vis n k) mo Q ->
  (forall rsp mo' evs a, nstep n mo rsp mo' evs -> k rsp = Ret (Ok a) -> Q a mo' -> R a mo' /\ live mo' <= B) ->
  etwl B (Vis n k) mo (fun a mo' => Q a mo' /\ R a mo').
Proof.
  intros Hf Hn H HR. cbn in H |- *. destruct H as [_ Hk]. split; [exact Hn|]. intros rsp mo' evs Hst. specialize (Hk rsp mo' evs Hst). specialize (Hf rsp).
  destruct (k rsp) as [[|a]|n' k'] eqn:Ek; cbn in Hk |- *; [destruct Hk| | destruct Hf].
  destruct (HR rsp mo' evs a Hst Ek Hk) as [HRa HB]. auto.
Qed.


Definition BOUND0 (L : mled) (e : ev) (B : Z) : Prop :=
  forall z, answer_ok L e z = true -> gm (event_post L e z) + BB (event_post L e z) <= B.

(* [comment removed for export] *)
Definition is_map0 (e : ev) : bool :=
  match e with EMmap _ _ _ flags => Z.land flags MAP_FIXED =? 0 | _ => false end.

Definition REQ (L : mled) (e : ev) (B : Z) : Prop :=
  match e with
  | EMmap _ len _ flags =>
      if Z.land flags MAP_FIXED =? 0 then mmap_len len <= SMALLREQ \/ gm L + BB L + mmap_len len <= B else True
  | _ => True
  end.

Definition BOUND (L : mled) (e : ev) (B : Z) : Prop := BOUND0 L e B /\ REQ L e B.

Lemma REQ_not_map0 L e B : is_map0 e = false -> REQ L e B.
Proof. destruct e as [| ? ? ? flags | | | | ]; cbn; try (intros; exact I). intros H. rewrite H. exact I. Qed.

Lemma BOUND_intro0 L e B : is_map0 e = false -> BOUND0 L e B -> BOUND L e B.
Proof. intros H1 H2. split; [exact H2| exact (REQ_not_map0 L e B H1)]. Qed.

Lemma REQ_mono L e B B' : REQ L e B -> B <= B' -> REQ L e B'.
Proof.
  destruct e as [| ? len ? flags | | | | ]; cbn; try (intros; exact I).
  destruct (Z.land flags MAP_FIXED =? 0); [|intros; exact I]. intros [H|H] HB; [left; exact H| right; lia].
Qed.

(* [comment removed for export] *)
Lemma BOUND0_now_mmap0 L len prot B : BOUND0 L (EMmap 0 len prot MAPF) B -> gm L + BB L <= B.
Proof.
  intros HB. specialize (HB (TWO64 - ENOMEM)). unfold answer_ok, event_post in HB.
  change (Z.land MAPF MAP_FIXED =? 0) with true in HB. cbn iota in HB.
  change (is_err (TWO64 - ENOMEM)) with true in HB. cbn iota in HB.
  apply HB. unfold mmap_answer_ok. change (is_errno_form (TWO64 - ENOMEM)) with true. reflexivity.
Qed.

Lemma BOUND0_now_mprotect L a n prot B : BOUND0 L (EMprotect a n prot) B -> gm L + BB L <= B.
Proof.
  intros HB. specialize (HB (TWO64 - ENOMEM)). unfold answer_ok, event_post in HB.
  change ((TWO64 - ENOMEM =? 0) || (TWO64 - ENOMEM =? TWO64 - ENOSYS)) with false in HB. cbn iota in HB.
  apply HB. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma noerr_mmap0 B L pbrk mo len prot :
  KL L pbrk mo -> LI L mo -> B <= KLIM -> 0 < len < LEN_MAX -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  BOUND L (EMmap 0 len prot MAPF) B -> node_noerr (NMmap 0 len prot MAPF) mo.
Proof.
  intros HK HL HBK Hlen Hprot [HB HR] _ rsp mo' evs Hst.
  pose proof (BOUND0_now_mmap0 L len prot B HB) as H0. pose proof (LI_elim _ _ HL) as H1.
  cbn [REQ] in HR. change (Z.land MAPF MAP_FIXED =? 0) with true in HR. cbn iota in HR.
  unfold LEN_MAX in Hlen.
  apply (gk_mmap_noerr L pbrk mo len prot rsp mo' evs HK (LI_gk _ _ HL)); [lia| lia| exact Hprot| | exact Hst].
  destruct HR as [HR|HR]; [left; exact HR| right; lia].
Qed.

Lemma noerr_mprotect B L pbrk mo b l k :
  KL L pbrk mo -> LI L mo -> B <= KLIM -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  BOUND L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) B -> node_noerr (NMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) mo.
Proof.
  intros HK HL HBK Hin Hk [HB _] rsp mo' evs Hst. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk.
  pose proof (BOUND0_now_mprotect L _ _ _ B HB) as H0. pose proof (LI_elim _ _ HL) as H1.
  apply (nstep_mprotect_noerr (b + (1 + k) * PGSZ) mo rsp mo' evs); [unfold PGSZ in *; lia| unfold PGSZ in *; lia| | | exact Hst].
  - rewrite Z.mod_add; [exact A3| unfold PGSZ; lia].
  - apply gk_mprotect_budget; [exact (minv_clean _ (kl_minv _ _ _ HK))| exact (LI_gk _ _ HL)| lia].
Qed.

End WithCeiling.
Ltac flat_shape W :=
  unfold mbind, msys, mret, mget, mupd, enode, ebind in W |- *; cbn [ITree.bind fst snd] in W |- *.
Section WithCeiling. Context {CE__ : Ceiling}.

Theorem ev_step_L B L e G s0 : frame_ok G -> event_pre L e -> B <= KLIM ->
  mspecL B (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo /\ BOUND L e B) (ev_step e)
          (fun z s mo => ev_step_post L e G s0 z s mo /\ LI (event_post L e z) mo).
Proof.
  intros HG Hpre HBK s mo (-> & HK & HLI & HGs & HB).
  pose proof (ev_step_spec L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as W.
  assert (FIN : forall z mo', answer_ok L e z = true -> LI (event_post L e z) mo' -> live mo' <= B).
  { intros z mo' Ha HL'. apply LI_elim in HL'. unfold live. specialize (proj1 HB z Ha). lia. }
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - (* [comment removed for export] *)
    unfold ev_step in W |- *.
    destruct (Z.eqb_spec req 0) as [->|NZ].
    + flat_shape W. eapply vis_flat_L; [| exact I| exact W|].
      { intros rsp. destruct (dec_brk0 rsp); reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      destruct (dec_brk0 rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate]. assert (Ez : z = x) by congruence. subst x.
      destruct Hpre as [[_ Hph]|[(cur & Hph & E)|(b & l & Hph & Hreg & E)]].
      2:{ exfalso. pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as (Ecur & _). pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia. }
      2:{ exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia. }
      pose proof (li_brk0 L (ps_brk s0) mo rsp mo' evs z HK HLI Hph Hst) as HL'.
      change (event_post L (EBrk 0) z) with (set_brkph (BPQueried z) L). split; [exact HL'| exact (FIN z mo' Hans HL')].
    + flat_shape W. eapply vis_flat_L; [| exact I| exact W|].
      { intros rsp. destruct (dec_brk (ps_brk s0) req rsp) as [[|]|]; reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      destruct (dec_brk (ps_brk s0) req rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
      assert (Ez : z = match x with BrkGrown => req | BrkSame => ps_brk s0 end) by (destruct x; cbn in Ek; congruence).
      destruct Hpre as [[E _]|Hpre]; [exfalso; exact (NZ E)|].
      pose proof (li_brk_grow L (ps_brk s0) mo rsp mo' evs req x HK HLI Hpre Hst Hd) as HL'. rewrite <- Ez in HL'.
      split; [exact HL'| exact (FIN z mo' Hans HL')].
  - (* [comment removed for export] *)
    unfold ev_step in W |- *.
    destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in *. cbn iota in W |- *.
      destruct Hprot as [-> | ->].
      * change (PROT_NONE =? 0) with true in *. cbn iota in W |- *. flat_shape W.
        eapply vis_flat_L; [| exact (noerr_mmap0 B L (ps_brk s0) mo len PROT_NONE HK HLI HBK Hlen (or_introl eq_refl) HB)| exact W|].
        { intros rsp. destruct (dec_mmap_none len [] rsp); reflexivity. }
        intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
        destruct (dec_mmap_none len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
        assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
        pose proof (li_mmap_none L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
        split; [exact HL'| exact (FIN _ mo' Hans HL')].
      * change (PROT_RW =? 0) with false in *. cbn iota in W |- *. flat_shape W.
        eapply vis_flat_L; [| exact (noerr_mmap0 B L (ps_brk s0) mo len PROT_RW HK HLI HBK Hlen (or_intror eq_refl) HB)| exact W|].
        { intros rsp. destruct (dec_mmap len [] rsp); reflexivity. }
        intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
        destruct (dec_mmap len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
        assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
        pose proof (li_mmap_rw L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
        split; [exact HL'| exact (FIN _ mo' Hans HL')].
    + change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true in *. cbn iota in W |- *. flat_shape W.
      eapply vis_flat_L; [| intros Hfx; exfalso; cbv in Hfx; discriminate Hfx| exact W|].
      { intros rsp. destruct (dec_mmap_fixed (round_up_pg cur) PGSZ rsp); reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      pose proof (li_mmap_fixed L (ps_brk s0) mo rsp mo' evs cur z HK HLI Hph Hst) as HL'.
      split; [exact HL'| exact (FIN _ mo' Hans HL')].
  - (* [comment removed for export] *)
    unfold ev_step in W |- *. destruct Hpre as (Hq & l0 & Hin & Hlen). flat_shape W. eapply vis_flat_L; [| exact I| exact W|].
    { intros rsp. destruct (dec_munmap addr len rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    pose proof (li_munmap L (ps_brk s0) mo rsp mo' evs addr l0 len z HK HLI Hin Hlen Hst) as HL'.
    split; [exact HL'| exact (FIN _ mo' Hans HL')].
  - (* [comment removed for export] *)
    unfold ev_step in W |- *. destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). flat_shape W.
    eapply vis_flat_L; [| exact (noerr_mprotect B L (ps_brk s0) mo b l k HK HLI HBK Hin Hk HB)| exact W|].
    { intros rsp. destruct (dec_mprotect_rw (b + (1 + k) * PGSZ) PGSZ rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    pose proof (li_mprotect L (ps_brk s0) mo rsp mo' evs b l k z HK HLI Hin Hk Hst) as HL'.
    split; [exact HL'| exact (FIN _ mo' Hans HL')].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint qtree {R} (B : Z) (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ BOUND L e B /\ forall z, answer_ok L e z = true -> qtree B (event_post L e z) (k z) Post
  end.

Lemma qtree_mono {R} B L (t : stree ev Z R) (P P' : mled -> R -> Prop) :
  qtree B L t P -> (forall L' r, P L' r -> P' L' r) -> qtree B L t P'.
Proof.
  revert L. induction t as [r|e k IH]; intros L H HP; cbn in *; [apply HP; exact H|].
  destruct H as (He & HB & Hk). split; [exact He|]. split; [exact HB|]. intros z Hz. apply IH; [apply Hk; exact Hz| exact HP].
Qed.

Lemma qtree_ctree_ok {R} B L (t : stree ev Z R) P : qtree B L t P -> ctree_ok L t P.
Proof.
  revert L. induction t as [r|e k IH]; intros L H; cbn in *; [exact H|].
  destruct H as (He & HB & Hk). split; [exact He|]. intros z Hz. apply IH. apply Hk. exact Hz.
Qed.

Theorem membedL {R} B (t : stree ev Z R) : forall (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  B <= KLIM ->   (* [comment removed for export] *)
  frame_ok G -> qtree B L t Post ->
  mspecL B (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo) (membed t)
         (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ LI L' mo /\ G s mo
                        /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  induction t as [r|e k IH]; intros Post G L s0 HBK HG Hq.
  - cbn [membed]. apply mspecL_ret. intros s mo (-> & HK & HL & HGs). exists L. split; [constructor|]. cbn in Hq. split; [exact Hq|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. auto.
  - cbn [membed]. cbn in Hq. destruct Hq as (Hpre & HB & Hk).
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (ev_step_L B L e G s0 HG Hpre HBK)|]. intros s mo (-> & HK & HL & HGs). split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs| exact HB]. }
    intros z. apply mspecL_pointwise. intros s1 mo1 [(Hans & HK1 & HG1 & Hm & Hfa & Hso) HL1].
    eapply mspecL_conseq; [apply (IH z Post G (event_post L e z) s1 HBK HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & HL' & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
      split; [exact HP|]. split; [exact HK|]. split; [exact HL'|]. split; [exact HG'|]. repeat split; congruence.
Qed.

End WithCeiling.
