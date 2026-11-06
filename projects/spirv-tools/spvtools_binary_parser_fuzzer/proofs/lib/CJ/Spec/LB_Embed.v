(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KLink LB_Logic LB_Kernel.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma vis_flat_L {A} B n (k : resp -> itree node (exc A)) mo (Q : A -> Model -> Prop) (R : A -> Model -> Prop) :
  (forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end) ->
  etwf (Vis n k) mo Q ->
  (forall rsp mo' evs a, nstep n mo rsp mo' evs -> k rsp = Ret (Ok a) -> Q a mo' -> R a mo' /\ live mo' <= B) ->
  etwl B (Vis n k) mo (fun a mo' => Q a mo' /\ R a mo').
Proof.
  intros Hf H HR. cbn in H |- *. destruct H as [_ Hk]. intros rsp mo' evs Hst. specialize (Hk rsp mo' evs Hst). specialize (Hf rsp).
  destruct (k rsp) as [[|a]|n' k'] eqn:Ek; cbn in Hk |- *; [destruct Hk| | destruct Hf].
  destruct (HR rsp mo' evs a Hst Ek Hk) as [HRa HB]. auto.
Qed.

Definition BOUND (L : mled) (e : ev) (B : Z) : Prop :=
  forall z, answer_ok L e z = true -> gm (event_post L e z) + BB (event_post L e z) <= B.
End AC_1.

Ltac flat_shape W :=
  unfold mbind, msys, mret, mget, mupd, enode, ebind in W |- *; cbn [ITree.bind fst snd] in W |- *.
Section AC_2. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Theorem ev_step_L B L e G s0 : frame_ok G -> event_pre L e ->
  mspecL B (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo /\ BOUND L e B) (ev_step e)
          (fun z s mo => ev_step_post L e G s0 z s mo /\ LI (event_post L e z) mo).
Proof.
  intros HG Hpre s mo (-> & HK & HLI & HGs & HB).
  pose proof (ev_step_spec L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as W.
  assert (FIN : forall z mo', answer_ok L e z = true -> LI (event_post L e z) mo' -> live mo' <= B).
  { intros z mo' Ha HL'. apply LI_elim in HL'. unfold live. specialize (HB z Ha). lia. }
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  -
    unfold ev_step in W |- *.
    destruct (Z.eqb_spec req 0) as [->|NZ].
    + flat_shape W. eapply vis_flat_L; [| exact W|].
      { intros rsp. destruct (dec_brk0 rsp); reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      destruct (dec_brk0 rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate]. assert (Ez : z = x) by congruence. subst x.
      destruct Hpre as [[_ Hph]|[(cur & Hph & E)|(b & l & Hph & Hreg & E)]].
      2:{ exfalso. pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as (Ecur & _). pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia. }
      2:{ exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia. }
      pose proof (li_brk0 L (ps_brk s0) mo rsp mo' evs z HK HLI Hph Hst) as HL'.
      change (event_post L (EBrk 0) z) with (set_brkph (BPQueried z) L). split; [exact HL'| exact (FIN z mo' Hans HL')].
    + flat_shape W. eapply vis_flat_L; [| exact W|].
      { intros rsp. destruct (dec_brk (ps_brk s0) req rsp) as [[|]|]; reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      destruct (dec_brk (ps_brk s0) req rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
      assert (Ez : z = match x with BrkGrown => req | BrkSame => ps_brk s0 end) by (destruct x; cbn in Ek; congruence).
      destruct Hpre as [[E _]|Hpre]; [exfalso; exact (NZ E)|].
      pose proof (li_brk_grow L (ps_brk s0) mo rsp mo' evs req x HK HLI Hpre Hst Hd) as HL'. rewrite <- Ez in HL'.
      split; [exact HL'| exact (FIN z mo' Hans HL')].
  -
    unfold ev_step in W |- *.
    destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in *. cbn iota in W |- *.
      destruct Hprot as [-> | ->].
      * change (PROT_NONE =? 0) with true in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_L; [| exact W|].
        { intros rsp. destruct (dec_mmap_none len [] rsp); reflexivity. }
        intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
        destruct (dec_mmap_none len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
        assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
        pose proof (li_mmap_none L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
        split; [exact HL'| exact (FIN _ mo' Hans HL')].
      * change (PROT_RW =? 0) with false in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_L; [| exact W|].
        { intros rsp. destruct (dec_mmap len [] rsp); reflexivity. }
        intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
        destruct (dec_mmap len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
        assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
        pose proof (li_mmap_rw L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
        split; [exact HL'| exact (FIN _ mo' Hans HL')].
    + change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_L; [| exact W|].
      { intros rsp. destruct (dec_mmap_fixed (round_up_pg cur) PGSZ rsp); reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      pose proof (li_mmap_fixed L (ps_brk s0) mo rsp mo' evs cur z HK HLI Hph Hst) as HL'.
      split; [exact HL'| exact (FIN _ mo' Hans HL')].
  -
    unfold ev_step in W |- *. destruct Hpre as (Hq & l0 & Hin & Hlen). flat_shape W. eapply vis_flat_L; [| exact W|].
    { intros rsp. destruct (dec_munmap addr len rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    pose proof (li_munmap L (ps_brk s0) mo rsp mo' evs addr l0 len z HK HLI Hin Hlen Hst) as HL'.
    split; [exact HL'| exact (FIN _ mo' Hans HL')].
  -
    unfold ev_step in W |- *. destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). flat_shape W. eapply vis_flat_L; [| exact W|].
    { intros rsp. destruct (dec_mprotect_rw (b + (1 + k) * PGSZ) PGSZ rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    pose proof (li_mprotect L (ps_brk s0) mo rsp mo' evs b l k z HK HLI Hin Hk Hst) as HL'.
    split; [exact HL'| exact (FIN _ mo' Hans HL')].
Qed.

Fixpoint qtree {R} (B : Z) (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ BOUND L e B /\ forall z, answer_ok L e z = true -> qtree B (event_post L e z) (k z) Post
  end.

Lemma qtree_ctree_ok {R} B L (t : stree ev Z R) P : qtree B L t P -> ctree_ok L t P.
Proof.
  revert L. induction t as [r|e k IH]; intros L H; cbn in *; [exact H|].
  destruct H as (He & HB & Hk). split; [exact He|]. intros z Hz. apply IH. apply Hk. exact Hz.
Qed.

Theorem membedL {R} B (t : stree ev Z R) : forall (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  frame_ok G -> qtree B L t Post ->
  mspecL B (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo) (membed t)
         (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ LI L' mo /\ G s mo
                        /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  induction t as [r|e k IH]; intros Post G L s0 HG Hq.
  - cbn [membed]. apply mspecL_ret. intros s mo (-> & HK & HL & HGs). exists L. split; [constructor|]. cbn in Hq. split; [exact Hq|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. auto.
  - cbn [membed]. cbn in Hq. destruct Hq as (Hpre & HB & Hk).
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (ev_step_L B L e G s0 HG Hpre)|]. intros s mo (-> & HK & HL & HGs). split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs| exact HB]. }
    intros z. apply mspecL_pointwise. intros s1 mo1 [(Hans & HK1 & HG1 & Hm & Hfa & Hso) HL1].
    eapply mspecL_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & HL' & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
      split; [exact HP|]. split; [exact HK|]. split; [exact HL'|]. split; [exact HG'|]. repeat split; congruence.
Qed.

End AC_2.
