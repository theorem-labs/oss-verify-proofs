(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA SysStepF StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase F_apoison APoisonR_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma poison0_noevent : forall R (addr size : Z) (k : AM R),
  0 <= addr -> 0 < size -> addr + size <= 2^47 ->
  poison0 addr size k = k.
Proof.
  intros R addr size k A0 S0 HE. unfold poison0.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=17246068742.829784463721.842763520060.800000700800<S2A02HESS2S0".
replace (size =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv zeta.
  replace (SHADOW_OFF + Z.shiftr (addr + size - 8) 3 + 1 - (SHADOW_OFF + Z.shiftr addr 3) <? CLEAR_SHADOW_MMAP_THRESHOLD) with true; [reflexivity|].
  symmetry. apply Z.ltb_lt. unfold CLEAR_SHADOW_MMAP_THRESHOLD. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma premap_cells_frame_hi : forall m m' W,
  premap_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> premap_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold premap_cells, AIMG_HI in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & (cb & P6) & P7).
  repeat split; try (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
  exists cb. eapply rw_cells_transport; [exact P6 | exact MU | exact WM | apply D; cbn; lia].
Qed.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Theorem poison_remap_proof : poison_remap_stmt.
Proof.
  unfold poison_remap_stmt.
  intros R k Q RNG. intros until junk. intros ST CEIL LO MI PC PRC RR -> -> -> AL SL SZ HI HE BIG DST RIMG RSTK RSH KONT.
  unfold PZR_STACK in *.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'. pose proof atop_range as ATR.
  Local Ltac2 Set LiaHints.tbl := fun () => "00;0>15973358331.7 16342827646.7 17978678919.7 29786411260.6033701821946.8235383312959.9 38043130688.6146910986289.8257018341433.6157622410744.8465005110394.6100000400900=00>00K00Z00^00c00d00g00lS2HES3HI'S2SZSS4CEIL2LO3ATRS2AL2SL3HI'3ATRS2LOS3SHBSS1HS3SHB".
rewrite poison0_noevent by (clear -HI' SZ HE ATR; lia).
  assert (SHB : 0x800b6c00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -AL SL SZ HI' HE ATR. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  eapply implF_evtF.
  { eapply (poison_shadow_spec RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size 0 lo junk);
      try eassumption; try reflexivity; try lia.
    all: try (intros _; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -HE SZ HI' ATR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). }
  intros ms' PO. unfold poison_post in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & DST').
  eapply KONT. unfold premap_post, PZR_STACK.
  split; [apply fp_le_refl|]. split; [intros BW; exact BW|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split. { change (0 mod 256) with 0 in DST'. unfold zeros. exact DST'. }
  split; [exact RSH|].
  split.
  - eapply poison_cells_frame; [exact PC | exact MU | exact WM |].
    apply Forall_cons; [cbn; unfold AIMG_HI; lia|]. apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
  - eapply premap_cells_frame_hi; [exact PRC | exact MU | exact WM |].
    apply Forall_cons; [cbn; unfold AIMG_HI; lia|]. apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition poison_remap : poison_remap_stmt := poison_remap_proof.
End CANSEC2.
