(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_vfmatch_F HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Notation METHOD_TAB := 0x2b3b8%Z.
Notation FMT_REQ09 := 0x10331%Z.
Notation FMT_REQ := 0x10423%Z.

Definition ppFS_ (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition ctl8 (err hack pos entp clen csz esp : Z) : list cell :=
  [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)].

Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.

Section SEGS.
Context {HCEIL : HasCeiling}.
  Variables (P q lo TP : Z).
  Hypothesis QLO : (lo + 16 <= q)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis QP : (q + 208 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^62)%Z.
  Hypothesis TPR : (0 <= TP < 2^64)%Z.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m :=
    (MS (mkR x1 (wz q) gp (wz TP) t0 t1 t2 (wz P) (wz (P + 480)) a0 a1 a2 a3 a4 a5 a6 a7
            (wz (-1)) (wz 47) (wz 2) (wz FMT_REQ09) (wz METHOD_TAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
  Hypothesis PAL : (P mod 8 = 0)%Z.

  #[using="QLO LO0 QP PHI TPR PAL"] Lemma pp_entry : forall ra gp t0 t1 t2 s0 s1 a0r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
    stk rsegs m lo (q + 208) -> mem_inv rsegs m -> a0r = wz P ->
    evt rsegs (fun ms' => exists m' a0' a1' a2' (j1 j2 : list byte),
        ms' = PRS 0x15c9c ra t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s7 s9 t3 t4 t5 t6 gp F fc m'
        /\ munch [(q, q + 208)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo q
        /\ rw_cells rsegs m' q [CB 16 j1]
        /\ rw_cells rsegs m' (q + 16) [C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (P + 8)); C8 (wz (2^64 - 1 - METHOD_TAB)); C8 (wz FMT_REQ)]
        /\ rw_cells rsegs m' (q + 56) [CB 48 j2]
        /\ rw_cells rsegs m' (q + 104) (ppFS_ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      (MS (mkR ra (wz (q + 208)) gp (wz TP) t0 t1 t2 s0 s1 a0r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x15bec) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI ->.
    pose proof (munch_refl [(q, q + 208)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (E : bv_unsigned (wz (q + 208)) = q + 208) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 208%nat ST. rewrite !E in *.
    replace (q + 208 + -208)%Z with q in FR by lia. replace (q + 208 + -208)%Z with q in ST by lia.
    do 14 sstep.
    ub_null. zstep. ub_align.
    zstep. zstep. sstep. zstep. sstep. zstep. sstep.
    do 11 zstep. sstep. zstep. sstep. zstep. zstep.
    name_junk FR.
    split_chunk FR 1%nat Q0 R1. split_chunk R1 5%nat Q16 R2. split_chunk R2 1%nat Q56 FSH.
    apply evt_done. eexists _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact Q0|]. split; [exact Q16|]. split; [exact Q56| exact FSH].
  Qed.

  Definition pp_target (pos : Z) : Z :=
    if (pos =? 2)%Z then 0x14c4c else if (pos =? 3)%Z then 0x15704 else if (pos =? 1)%Z then 0x14904
    else if (pos =? 0)%Z then 0x15cb8 else 0x15fe0.
  Definition pp_ra (pos : Z) (x1 : word) : word :=
    if (pos =? 2)%Z then wz 0x15c98 else if (pos =? 3)%Z then wz 0x15db0 else if (pos =? 1)%Z then wz 0x15cb4 else x1.
  Definition pp_a0 (pos : Z) : word :=
    if (pos =? 0)%Z then wz 0 else if (pos =? 4)%Z then wz 3 else wz P.

  #[using="TPR"] Lemma pp_head : forall (err hack pos entp clen csz esp : Z) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (P + 440) (ctl8 err hack pos entp clen csz esp) -> (0 <= pos <= 4)%Z ->
    evt rsegs (fun ms' => ms' = PRS (pp_target pos) (pp_ra pos x1) t0 t1 t2 (pp_a0 pos) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m)
      (PRS 0x15c9c x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m).
  Proof.
    intros until m. intros MI CTL POS. unfold ctl8 in CTL.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. rewrite sx32_lit by lia.
    assert (CS : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3 \/ pos = 4) by lia.
    destruct CS as [-> | [-> | [-> | [-> | ->]]]]; unfold pp_target, pp_ra, pp_a0; cbn [Z.eqb Pos.eqb].
    - zstep. lit_branch. zstep. lit_branch. apply evt_done. reflexivity.
    - zstep. lit_branch. zstep. lit_branch. zstep. lit_branch. zstep. zstep. apply evt_done. reflexivity.
    - zstep. lit_branch. zstep. lit_branch. zstep. zstep. apply evt_done. reflexivity.
    - zstep. lit_branch. zstep. lit_branch. zstep. lit_branch. zstep. zstep. apply evt_done. reflexivity.
    - zstep. lit_branch. zstep. lit_branch. zstep. lit_branch. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="TPR"] Lemma pp_join : forall (r : Z) x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp (F : bvmap 5 word) fc m,
    (0 <= r <= 5)%Z ->
    evt rsegs (fun ms' => (r = 4 /\ ms' = PRS 0x15c9c x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m)
                       \/ (r <> 4 /\ ms' = PRS 0x15fe0 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m))
      (PRS 0x15c98 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m).
  Proof.
    intros until m. intros RR. clear QLO LO0 QP PHI PAL. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K.
    - apply evt_done. right. split; [lia| reflexivity].
    - apply evt_done. left. split; [lia| reflexivity].
  Qed.

  #[using="Type"] Lemma pp_j1 : forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS 0x15c98 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m)
      (PRS 0x15cb4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m).
  Proof. intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. apply evt_done. reflexivity. Qed.
  #[using="Type"] Lemma pp_j2 : forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS 0x15c98 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m)
      (PRS 0x15db0 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m).
  Proof. intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. apply evt_done. reflexivity. Qed.
  #[using="Type"] Lemma pp_default : forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS 0x15fe0 x1 t0 t1 t2 (wz 3) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m)
      (PRS 0x15fdc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m).
  Proof. intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. apply evt_done. reflexivity. Qed.

  Definition ppFX_ (m : mem) : Prop :=
    (exists j1, rw_cells rsegs m q [CB 16 j1])
    /\ rw_cells rsegs m (q + 16) [C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (P + 8)); C8 (wz (2^64 - 1 - METHOD_TAB)); C8 (wz FMT_REQ)]
    /\ (exists j2, rw_cells rsegs m (q + 56) [CB 48 j2]).

  #[using="QLO TPR"] Lemma pp_epi : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> rw_cells rsegs m (q + 104) (ppFS_ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> ppFX_ m ->
    evt rsegs (fun ms' => ms' = MS (mkR ra (wz (q + 208)) gp (wz TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom rsegs)
                          /\ stk rsegs m lo (q + 208))
      (PRS 0x15fe0 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m).
  Proof.
    intros until m. intros ST MI FSH FX. unfold ppFS_ in FSH. destruct FX as ([j1 Q0] & Q16 & [j2 Q56]).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    do 13 zstep. zstep. zstep.
    eapply stk_release in Q0; [| exact ST| lia]. clear ST. release_all_ lo.
    apply evt_done. split; [reflexivity|]. lazymatch goal with H : stk rsegs m lo _ |- _ => exact H end.
  Qed.
End SEGS.
