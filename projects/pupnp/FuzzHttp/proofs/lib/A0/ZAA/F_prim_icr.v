(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim ATacA.
Import ListNotations.
Open Scope Z_scope.

Ltac run_to stop :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with stop => fail | _ => sstep end
          | |- evt _ _ (MS _ _ _ _ _ _ _) => lit_branch
          end).

Section IC.
  Context {HC : HasCeiling}.
  Variables (ra sp gp tp s0 s1 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variable THR : Z.
  Hypothesis THR_OK : 0 < THR /\ THR + 4096 <= 2^47.
  Notation CB := (THR + 208).

  Notation STi pc mm xa1 xa3 xa5 xt3 xt4 xt5 :=
    (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 (wz (THR + 208)) xa1 a2 xa3 a4 xa5 (wz 15) (wz 1024)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 t6)
        F_ (wz pc) fc None mm (seg_rom asegs)).

  Definition ic_post (pc off a1' a3' a5' mx sz : Z) (cnt : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists xt3 xt4 xt5 m', ms' = STi pc m' (wz (THR + a1')) (wz a3') (wz a5') xt3 xt4 xt5
      /\ munch [(THR + off + 4, THR + off + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (THR + off) [C4 cnt; C4 (wz mx); C8 (wz sz)].

  #[using="THR_OK"] Lemma ic_r_01 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 288) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 288 376 64 (-14) 16 32 cnt m)
      (STi 0x384ec m (wz (THR + 296)) (wz 32) (wz (-15)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 288 + 4, THR + 288 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_02 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 368) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 368 456 96 (-13) 16 64 cnt m)
      (STi 0x384ec m (wz (THR + 376)) (wz 64) (wz (-14)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 368 + 4, THR + 368 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_03 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 448) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 448 536 128 (-12) 16 96 cnt m)
      (STi 0x384ec m (wz (THR + 456)) (wz 96) (wz (-13)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 448 + 4, THR + 448 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_04 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 528) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 528 616 160 (-11) 16 128 cnt m)
      (STi 0x384ec m (wz (THR + 536)) (wz 128) (wz (-12)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 528 + 4, THR + 528 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_05 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 608) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 608 696 192 (-10) 12 160 cnt m)
      (STi 0x384ec m (wz (THR + 616)) (wz 160) (wz (-11)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 608 + 4, THR + 608 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_06 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 688) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 688 776 224 (-9) 10 192 cnt m)
      (STi 0x384ec m (wz (THR + 696)) (wz 192) (wz (-10)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 688 + 4, THR + 688 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_07 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 768) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 768 856 256 (-8) 8 224 cnt m)
      (STi 0x384ec m (wz (THR + 776)) (wz 224) (wz (-9)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 768 + 4, THR + 768 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_08 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 848) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 848 936 288 (-7) 8 256 cnt m)
      (STi 0x384ec m (wz (THR + 856)) (wz 256) (wz (-8)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 848 + 4, THR + 848 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_09 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 928) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 928 1016 320 (-6) 6 288 cnt m)
      (STi 0x384ec m (wz (THR + 936)) (wz 288) (wz (-7)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 928 + 4, THR + 928 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_10 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1008) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1008 1096 352 (-5) 6 320 cnt m)
      (STi 0x384ec m (wz (THR + 1016)) (wz 320) (wz (-6)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1008 + 4, THR + 1008 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_11 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1088) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1088 1176 384 (-4) 4 352 cnt m)
      (STi 0x384ec m (wz (THR + 1096)) (wz 352) (wz (-5)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1088 + 4, THR + 1088 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_12 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1168) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1168 1256 416 (-3) 4 384 cnt m)
      (STi 0x384ec m (wz (THR + 1176)) (wz 384) (wz (-4)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1168 + 4, THR + 1168 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_13 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1248) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1248 1336 448 (-2) 4 416 cnt m)
      (STi 0x384ec m (wz (THR + 1256)) (wz 416) (wz (-3)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1248 + 4, THR + 1248 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_14 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1328) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1328 1416 480 (-1) 4 448 cnt m)
      (STi 0x384ec m (wz (THR + 1336)) (wz 448) (wz (-2)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1328 + 4, THR + 1328 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_15 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1408) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1408 1496 512 (0) 4 480 cnt m)
      (STi 0x384ec m (wz (THR + 1416)) (wz 480) (wz (-1)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1408 + 4, THR + 1408 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_16 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1488) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1488 1576 544 (1) 4 512 cnt m)
      (STi 0x384ec m (wz (THR + 1496)) (wz 512) (wz (0)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1488 + 4, THR + 1488 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_17 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1568) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1568 1656 576 (2) 2 768 cnt m)
      (STi 0x384ec m (wz (THR + 1576)) (wz 544) (wz (1)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1568 + 4, THR + 1568 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_18 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1648) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1648 1736 608 (3) 2 1024 cnt m)
      (STi 0x384ec m (wz (THR + 1656)) (wz 576) (wz (2)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1648 + 4, THR + 1648 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_19 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1728) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1728 1816 640 (4) 2 1536 cnt m)
      (STi 0x384ec m (wz (THR + 1736)) (wz 608) (wz (3)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1728 + 4, THR + 1728 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_20 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1808) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1808 1896 672 (5) 2 2048 cnt m)
      (STi 0x384ec m (wz (THR + 1816)) (wz 640) (wz (4)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1808 + 4, THR + 1808 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_21 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1888) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1888 1976 704 (6) 2 3072 cnt m)
      (STi 0x384ec m (wz (THR + 1896)) (wz 672) (wz (5)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1888 + 4, THR + 1888 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_22 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 1968) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 1968 2056 736 (7) 2 4096 cnt m)
      (STi 0x384ec m (wz (THR + 1976)) (wz 704) (wz (6)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 1968 + 4, THR + 1968 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_23 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2048) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 2048 2136 768 (8) 2 6144 cnt m)
      (STi 0x384ec m (wz (THR + 2056)) (wz 736) (wz (7)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2048 + 4, THR + 2048 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_24 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2128) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 2128 2216 800 (9) 2 8192 cnt m)
      (STi 0x384ec m (wz (THR + 2136)) (wz 768) (wz (8)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2128 + 4, THR + 2128 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_25 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2208) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 2208 2296 832 (10) 2 12288 cnt m)
      (STi 0x384ec m (wz (THR + 2216)) (wz 800) (wz (9)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2208 + 4, THR + 2208 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_26 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2288) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 2288 2376 864 (11) 2 16384 cnt m)
      (STi 0x384ec m (wz (THR + 2296)) (wz 832) (wz (10)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2288 + 4, THR + 2288 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_27 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2368) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 2368 2456 896 (12) 2 24576 cnt m)
      (STi 0x384ec m (wz (THR + 2376)) (wz 864) (wz (11)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2368 + 4, THR + 2368 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_28 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2448) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 2448 2536 928 (13) 2 32768 cnt m)
      (STi 0x384ec m (wz (THR + 2456)) (wz 896) (wz (12)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2448 + 4, THR + 2448 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_29 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2528) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 2528 2616 960 (14) 2 49152 cnt m)
      (STi 0x384ec m (wz (THR + 2536)) (wz 928) (wz (13)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2528 + 4, THR + 2528 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_30 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2608) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x384ec 2608 2696 992 (15) 2 65536 cnt m)
      (STi 0x384ec m (wz (THR + 2616)) (wz 960) (wz (14)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2608 + 4, THR + 2608 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x384ec%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  #[using="THR_OK"] Lemma ic_r_31 : forall (m : mem) (cnt mx0 sz0 xt3 xt4 xt5 : word),
    rw_cells asegs m (THR + 2688) [C4 cnt; C4 mx0; C8 sz0] -> mem_inv asegs m ->
    evt asegs (ic_post 0x38540 2688 2776 1024 (16) 16 64 cnt m)
      (STi 0x384ec m (wz (THR + 2696)) (wz 992) (wz (15)) xt3 xt4 xt5).
  Proof.
    intros m cnt mx0 sz0 xt3 xt4 xt5 PC MI.
    pose proof (munch_refl [(THR + 2688 + 4, THR + 2688 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. run_to 0x38540%Z.
    apply evt_done. unfold ic_post. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  Variable AL : alayout.
  Hypothesis THR_EQ : at_thr (al_thread AL) = THR.
  #[using="THR_OK THR_EQ"] Lemma ic_r_all : forall (m : mem) (P : prim) xa1 xa3 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5,
    (forall c, 1 <= c <= 31 -> pcl_rep AL m false c (get_cls P c)) -> mem_inv asegs m ->
    evt asegs (fun ms' => exists xt3' xt4' xt5' m', ms' = STi 0x38540 m' (wz (THR + 2776)) (wz 1024) (wz 16) xt3' xt4' xt5'
                 /\ munch [(THR + 292, THR + 2704)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ (forall c, 1 <= c <= 31 -> pcl_rep AL m' true c (get_cls P c)))
      (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (wz (THR + 208)) xa1 a2 xa3 a4 xa5 xa6 xa7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 t6) F_ (wz 0x384a4) fc None m (seg_rom asegs)).
  Proof.
    intros m P xa1 xa3 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 FAM0 MI.
    pose proof (munch_refl [(THR + 292, THR + 2704)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (pcl_fam_start AL m P FAM0) as FAM. clear FAM0.
    do 9 zstep.

    destruct (FAM 1 ltac:(lia)) as [PC1 _]. unfold pcl_addr in PC1. rewrite THR_EQ in PC1.
    replace (THR + 208 + 80 * 1) with (THR + 288) in PC1 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC1.
    eapply evt_cut; [eapply (ic_r_01 _ _ _ _ _ _ _ PC1); assumption|].
    clear PC1. intros ms1 PO. destruct PO as (y3_1 & y4_1 & y5_1 & m1 & -> & MU1 & WM1 & MI1 & PC1).
    pose proof (pcl_fam_step AL _ _ P 1 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 1) with (THR + 288) by lia; exact MU1) WM1
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 1) with (THR + 288) by lia; exact PC1)) as FAM'.
    clear FAM PC1. rename FAM' into FAM. change (1 + 1) with 2 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU1; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU1) as MU'. clear MU MU1. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM1) as WM'. clear WM WM1. rename WM' into WM.
    clear MI.

    destruct (FAM 2 ltac:(lia)) as [PC2 _]. unfold pcl_addr in PC2. rewrite THR_EQ in PC2.
    replace (THR + 208 + 80 * 2) with (THR + 368) in PC2 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC2.
    eapply evt_cut; [eapply (ic_r_02 _ _ _ _ _ _ _ PC2); assumption|].
    clear PC2. intros ms2 PO. destruct PO as (y3_2 & y4_2 & y5_2 & m2 & -> & MU2 & WM2 & MI2 & PC2).
    pose proof (pcl_fam_step AL _ _ P 2 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 2) with (THR + 368) by lia; exact MU2) WM2
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 2) with (THR + 368) by lia; exact PC2)) as FAM'.
    clear FAM PC2. rename FAM' into FAM. change (2 + 1) with 3 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU2; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU2) as MU'. clear MU MU2. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM2) as WM'. clear WM WM2. rename WM' into WM.
    clear MI1.

    destruct (FAM 3 ltac:(lia)) as [PC3 _]. unfold pcl_addr in PC3. rewrite THR_EQ in PC3.
    replace (THR + 208 + 80 * 3) with (THR + 448) in PC3 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC3.
    eapply evt_cut; [eapply (ic_r_03 _ _ _ _ _ _ _ PC3); assumption|].
    clear PC3. intros ms3 PO. destruct PO as (y3_3 & y4_3 & y5_3 & m3 & -> & MU3 & WM3 & MI3 & PC3).
    pose proof (pcl_fam_step AL _ _ P 3 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 3) with (THR + 448) by lia; exact MU3) WM3
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 3) with (THR + 448) by lia; exact PC3)) as FAM'.
    clear FAM PC3. rename FAM' into FAM. change (3 + 1) with 4 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU3; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU3) as MU'. clear MU MU3. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM3) as WM'. clear WM WM3. rename WM' into WM.
    clear MI2.

    destruct (FAM 4 ltac:(lia)) as [PC4 _]. unfold pcl_addr in PC4. rewrite THR_EQ in PC4.
    replace (THR + 208 + 80 * 4) with (THR + 528) in PC4 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC4.
    eapply evt_cut; [eapply (ic_r_04 _ _ _ _ _ _ _ PC4); assumption|].
    clear PC4. intros ms4 PO. destruct PO as (y3_4 & y4_4 & y5_4 & m4 & -> & MU4 & WM4 & MI4 & PC4).
    pose proof (pcl_fam_step AL _ _ P 4 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 4) with (THR + 528) by lia; exact MU4) WM4
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 4) with (THR + 528) by lia; exact PC4)) as FAM'.
    clear FAM PC4. rename FAM' into FAM. change (4 + 1) with 5 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU4; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU4) as MU'. clear MU MU4. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM4) as WM'. clear WM WM4. rename WM' into WM.
    clear MI3.

    destruct (FAM 5 ltac:(lia)) as [PC5 _]. unfold pcl_addr in PC5. rewrite THR_EQ in PC5.
    replace (THR + 208 + 80 * 5) with (THR + 608) in PC5 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC5.
    eapply evt_cut; [eapply (ic_r_05 _ _ _ _ _ _ _ PC5); assumption|].
    clear PC5. intros ms5 PO. destruct PO as (y3_5 & y4_5 & y5_5 & m5 & -> & MU5 & WM5 & MI5 & PC5).
    pose proof (pcl_fam_step AL _ _ P 5 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 5) with (THR + 608) by lia; exact MU5) WM5
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 5) with (THR + 608) by lia; exact PC5)) as FAM'.
    clear FAM PC5. rename FAM' into FAM. change (5 + 1) with 6 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU5; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU5) as MU'. clear MU MU5. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM5) as WM'. clear WM WM5. rename WM' into WM.
    clear MI4.

    destruct (FAM 6 ltac:(lia)) as [PC6 _]. unfold pcl_addr in PC6. rewrite THR_EQ in PC6.
    replace (THR + 208 + 80 * 6) with (THR + 688) in PC6 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC6.
    eapply evt_cut; [eapply (ic_r_06 _ _ _ _ _ _ _ PC6); assumption|].
    clear PC6. intros ms6 PO. destruct PO as (y3_6 & y4_6 & y5_6 & m6 & -> & MU6 & WM6 & MI6 & PC6).
    pose proof (pcl_fam_step AL _ _ P 6 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 6) with (THR + 688) by lia; exact MU6) WM6
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 6) with (THR + 688) by lia; exact PC6)) as FAM'.
    clear FAM PC6. rename FAM' into FAM. change (6 + 1) with 7 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU6; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU6) as MU'. clear MU MU6. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM6) as WM'. clear WM WM6. rename WM' into WM.
    clear MI5.

    destruct (FAM 7 ltac:(lia)) as [PC7 _]. unfold pcl_addr in PC7. rewrite THR_EQ in PC7.
    replace (THR + 208 + 80 * 7) with (THR + 768) in PC7 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC7.
    eapply evt_cut; [eapply (ic_r_07 _ _ _ _ _ _ _ PC7); assumption|].
    clear PC7. intros ms7 PO. destruct PO as (y3_7 & y4_7 & y5_7 & m7 & -> & MU7 & WM7 & MI7 & PC7).
    pose proof (pcl_fam_step AL _ _ P 7 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 7) with (THR + 768) by lia; exact MU7) WM7
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 7) with (THR + 768) by lia; exact PC7)) as FAM'.
    clear FAM PC7. rename FAM' into FAM. change (7 + 1) with 8 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU7; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU7) as MU'. clear MU MU7. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM7) as WM'. clear WM WM7. rename WM' into WM.
    clear MI6.

    destruct (FAM 8 ltac:(lia)) as [PC8 _]. unfold pcl_addr in PC8. rewrite THR_EQ in PC8.
    replace (THR + 208 + 80 * 8) with (THR + 848) in PC8 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC8.
    eapply evt_cut; [eapply (ic_r_08 _ _ _ _ _ _ _ PC8); assumption|].
    clear PC8. intros ms8 PO. destruct PO as (y3_8 & y4_8 & y5_8 & m8 & -> & MU8 & WM8 & MI8 & PC8).
    pose proof (pcl_fam_step AL _ _ P 8 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 8) with (THR + 848) by lia; exact MU8) WM8
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 8) with (THR + 848) by lia; exact PC8)) as FAM'.
    clear FAM PC8. rename FAM' into FAM. change (8 + 1) with 9 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU8; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU8) as MU'. clear MU MU8. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM8) as WM'. clear WM WM8. rename WM' into WM.
    clear MI7.

    destruct (FAM 9 ltac:(lia)) as [PC9 _]. unfold pcl_addr in PC9. rewrite THR_EQ in PC9.
    replace (THR + 208 + 80 * 9) with (THR + 928) in PC9 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC9.
    eapply evt_cut; [eapply (ic_r_09 _ _ _ _ _ _ _ PC9); assumption|].
    clear PC9. intros ms9 PO. destruct PO as (y3_9 & y4_9 & y5_9 & m9 & -> & MU9 & WM9 & MI9 & PC9).
    pose proof (pcl_fam_step AL _ _ P 9 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 9) with (THR + 928) by lia; exact MU9) WM9
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 9) with (THR + 928) by lia; exact PC9)) as FAM'.
    clear FAM PC9. rename FAM' into FAM. change (9 + 1) with 10 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU9; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU9) as MU'. clear MU MU9. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM9) as WM'. clear WM WM9. rename WM' into WM.
    clear MI8.

    destruct (FAM 10 ltac:(lia)) as [PC10 _]. unfold pcl_addr in PC10. rewrite THR_EQ in PC10.
    replace (THR + 208 + 80 * 10) with (THR + 1008) in PC10 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC10.
    eapply evt_cut; [eapply (ic_r_10 _ _ _ _ _ _ _ PC10); assumption|].
    clear PC10. intros ms10 PO. destruct PO as (y3_10 & y4_10 & y5_10 & m10 & -> & MU10 & WM10 & MI10 & PC10).
    pose proof (pcl_fam_step AL _ _ P 10 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 10) with (THR + 1008) by lia; exact MU10) WM10
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 10) with (THR + 1008) by lia; exact PC10)) as FAM'.
    clear FAM PC10. rename FAM' into FAM. change (10 + 1) with 11 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU10; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU10) as MU'. clear MU MU10. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM10) as WM'. clear WM WM10. rename WM' into WM.
    clear MI9.

    destruct (FAM 11 ltac:(lia)) as [PC11 _]. unfold pcl_addr in PC11. rewrite THR_EQ in PC11.
    replace (THR + 208 + 80 * 11) with (THR + 1088) in PC11 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC11.
    eapply evt_cut; [eapply (ic_r_11 _ _ _ _ _ _ _ PC11); assumption|].
    clear PC11. intros ms11 PO. destruct PO as (y3_11 & y4_11 & y5_11 & m11 & -> & MU11 & WM11 & MI11 & PC11).
    pose proof (pcl_fam_step AL _ _ P 11 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 11) with (THR + 1088) by lia; exact MU11) WM11
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 11) with (THR + 1088) by lia; exact PC11)) as FAM'.
    clear FAM PC11. rename FAM' into FAM. change (11 + 1) with 12 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU11; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU11) as MU'. clear MU MU11. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM11) as WM'. clear WM WM11. rename WM' into WM.
    clear MI10.

    destruct (FAM 12 ltac:(lia)) as [PC12 _]. unfold pcl_addr in PC12. rewrite THR_EQ in PC12.
    replace (THR + 208 + 80 * 12) with (THR + 1168) in PC12 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC12.
    eapply evt_cut; [eapply (ic_r_12 _ _ _ _ _ _ _ PC12); assumption|].
    clear PC12. intros ms12 PO. destruct PO as (y3_12 & y4_12 & y5_12 & m12 & -> & MU12 & WM12 & MI12 & PC12).
    pose proof (pcl_fam_step AL _ _ P 12 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 12) with (THR + 1168) by lia; exact MU12) WM12
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 12) with (THR + 1168) by lia; exact PC12)) as FAM'.
    clear FAM PC12. rename FAM' into FAM. change (12 + 1) with 13 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU12; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU12) as MU'. clear MU MU12. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM12) as WM'. clear WM WM12. rename WM' into WM.
    clear MI11.

    destruct (FAM 13 ltac:(lia)) as [PC13 _]. unfold pcl_addr in PC13. rewrite THR_EQ in PC13.
    replace (THR + 208 + 80 * 13) with (THR + 1248) in PC13 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC13.
    eapply evt_cut; [eapply (ic_r_13 _ _ _ _ _ _ _ PC13); assumption|].
    clear PC13. intros ms13 PO. destruct PO as (y3_13 & y4_13 & y5_13 & m13 & -> & MU13 & WM13 & MI13 & PC13).
    pose proof (pcl_fam_step AL _ _ P 13 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 13) with (THR + 1248) by lia; exact MU13) WM13
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 13) with (THR + 1248) by lia; exact PC13)) as FAM'.
    clear FAM PC13. rename FAM' into FAM. change (13 + 1) with 14 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU13; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU13) as MU'. clear MU MU13. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM13) as WM'. clear WM WM13. rename WM' into WM.
    clear MI12.

    destruct (FAM 14 ltac:(lia)) as [PC14 _]. unfold pcl_addr in PC14. rewrite THR_EQ in PC14.
    replace (THR + 208 + 80 * 14) with (THR + 1328) in PC14 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC14.
    eapply evt_cut; [eapply (ic_r_14 _ _ _ _ _ _ _ PC14); assumption|].
    clear PC14. intros ms14 PO. destruct PO as (y3_14 & y4_14 & y5_14 & m14 & -> & MU14 & WM14 & MI14 & PC14).
    pose proof (pcl_fam_step AL _ _ P 14 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 14) with (THR + 1328) by lia; exact MU14) WM14
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 14) with (THR + 1328) by lia; exact PC14)) as FAM'.
    clear FAM PC14. rename FAM' into FAM. change (14 + 1) with 15 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU14; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU14) as MU'. clear MU MU14. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM14) as WM'. clear WM WM14. rename WM' into WM.
    clear MI13.

    destruct (FAM 15 ltac:(lia)) as [PC15 _]. unfold pcl_addr in PC15. rewrite THR_EQ in PC15.
    replace (THR + 208 + 80 * 15) with (THR + 1408) in PC15 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC15.
    eapply evt_cut; [eapply (ic_r_15 _ _ _ _ _ _ _ PC15); assumption|].
    clear PC15. intros ms15 PO. destruct PO as (y3_15 & y4_15 & y5_15 & m15 & -> & MU15 & WM15 & MI15 & PC15).
    pose proof (pcl_fam_step AL _ _ P 15 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 15) with (THR + 1408) by lia; exact MU15) WM15
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 15) with (THR + 1408) by lia; exact PC15)) as FAM'.
    clear FAM PC15. rename FAM' into FAM. change (15 + 1) with 16 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU15; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU15) as MU'. clear MU MU15. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM15) as WM'. clear WM WM15. rename WM' into WM.
    clear MI14.

    destruct (FAM 16 ltac:(lia)) as [PC16 _]. unfold pcl_addr in PC16. rewrite THR_EQ in PC16.
    replace (THR + 208 + 80 * 16) with (THR + 1488) in PC16 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC16.
    eapply evt_cut; [eapply (ic_r_16 _ _ _ _ _ _ _ PC16); assumption|].
    clear PC16. intros ms16 PO. destruct PO as (y3_16 & y4_16 & y5_16 & m16 & -> & MU16 & WM16 & MI16 & PC16).
    pose proof (pcl_fam_step AL _ _ P 16 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 16) with (THR + 1488) by lia; exact MU16) WM16
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 16) with (THR + 1488) by lia; exact PC16)) as FAM'.
    clear FAM PC16. rename FAM' into FAM. change (16 + 1) with 17 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU16; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU16) as MU'. clear MU MU16. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM16) as WM'. clear WM WM16. rename WM' into WM.
    clear MI15.

    destruct (FAM 17 ltac:(lia)) as [PC17 _]. unfold pcl_addr in PC17. rewrite THR_EQ in PC17.
    replace (THR + 208 + 80 * 17) with (THR + 1568) in PC17 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC17.
    eapply evt_cut; [eapply (ic_r_17 _ _ _ _ _ _ _ PC17); assumption|].
    clear PC17. intros ms17 PO. destruct PO as (y3_17 & y4_17 & y5_17 & m17 & -> & MU17 & WM17 & MI17 & PC17).
    pose proof (pcl_fam_step AL _ _ P 17 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 17) with (THR + 1568) by lia; exact MU17) WM17
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 17) with (THR + 1568) by lia; exact PC17)) as FAM'.
    clear FAM PC17. rename FAM' into FAM. change (17 + 1) with 18 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU17; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU17) as MU'. clear MU MU17. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM17) as WM'. clear WM WM17. rename WM' into WM.
    clear MI16.

    destruct (FAM 18 ltac:(lia)) as [PC18 _]. unfold pcl_addr in PC18. rewrite THR_EQ in PC18.
    replace (THR + 208 + 80 * 18) with (THR + 1648) in PC18 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC18.
    eapply evt_cut; [eapply (ic_r_18 _ _ _ _ _ _ _ PC18); assumption|].
    clear PC18. intros ms18 PO. destruct PO as (y3_18 & y4_18 & y5_18 & m18 & -> & MU18 & WM18 & MI18 & PC18).
    pose proof (pcl_fam_step AL _ _ P 18 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 18) with (THR + 1648) by lia; exact MU18) WM18
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 18) with (THR + 1648) by lia; exact PC18)) as FAM'.
    clear FAM PC18. rename FAM' into FAM. change (18 + 1) with 19 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU18; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU18) as MU'. clear MU MU18. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM18) as WM'. clear WM WM18. rename WM' into WM.
    clear MI17.

    destruct (FAM 19 ltac:(lia)) as [PC19 _]. unfold pcl_addr in PC19. rewrite THR_EQ in PC19.
    replace (THR + 208 + 80 * 19) with (THR + 1728) in PC19 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC19.
    eapply evt_cut; [eapply (ic_r_19 _ _ _ _ _ _ _ PC19); assumption|].
    clear PC19. intros ms19 PO. destruct PO as (y3_19 & y4_19 & y5_19 & m19 & -> & MU19 & WM19 & MI19 & PC19).
    pose proof (pcl_fam_step AL _ _ P 19 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 19) with (THR + 1728) by lia; exact MU19) WM19
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 19) with (THR + 1728) by lia; exact PC19)) as FAM'.
    clear FAM PC19. rename FAM' into FAM. change (19 + 1) with 20 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU19; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU19) as MU'. clear MU MU19. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM19) as WM'. clear WM WM19. rename WM' into WM.
    clear MI18.

    destruct (FAM 20 ltac:(lia)) as [PC20 _]. unfold pcl_addr in PC20. rewrite THR_EQ in PC20.
    replace (THR + 208 + 80 * 20) with (THR + 1808) in PC20 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC20.
    eapply evt_cut; [eapply (ic_r_20 _ _ _ _ _ _ _ PC20); assumption|].
    clear PC20. intros ms20 PO. destruct PO as (y3_20 & y4_20 & y5_20 & m20 & -> & MU20 & WM20 & MI20 & PC20).
    pose proof (pcl_fam_step AL _ _ P 20 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 20) with (THR + 1808) by lia; exact MU20) WM20
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 20) with (THR + 1808) by lia; exact PC20)) as FAM'.
    clear FAM PC20. rename FAM' into FAM. change (20 + 1) with 21 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU20; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU20) as MU'. clear MU MU20. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM20) as WM'. clear WM WM20. rename WM' into WM.
    clear MI19.

    destruct (FAM 21 ltac:(lia)) as [PC21 _]. unfold pcl_addr in PC21. rewrite THR_EQ in PC21.
    replace (THR + 208 + 80 * 21) with (THR + 1888) in PC21 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC21.
    eapply evt_cut; [eapply (ic_r_21 _ _ _ _ _ _ _ PC21); assumption|].
    clear PC21. intros ms21 PO. destruct PO as (y3_21 & y4_21 & y5_21 & m21 & -> & MU21 & WM21 & MI21 & PC21).
    pose proof (pcl_fam_step AL _ _ P 21 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 21) with (THR + 1888) by lia; exact MU21) WM21
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 21) with (THR + 1888) by lia; exact PC21)) as FAM'.
    clear FAM PC21. rename FAM' into FAM. change (21 + 1) with 22 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU21; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU21) as MU'. clear MU MU21. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM21) as WM'. clear WM WM21. rename WM' into WM.
    clear MI20.

    destruct (FAM 22 ltac:(lia)) as [PC22 _]. unfold pcl_addr in PC22. rewrite THR_EQ in PC22.
    replace (THR + 208 + 80 * 22) with (THR + 1968) in PC22 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC22.
    eapply evt_cut; [eapply (ic_r_22 _ _ _ _ _ _ _ PC22); assumption|].
    clear PC22. intros ms22 PO. destruct PO as (y3_22 & y4_22 & y5_22 & m22 & -> & MU22 & WM22 & MI22 & PC22).
    pose proof (pcl_fam_step AL _ _ P 22 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 22) with (THR + 1968) by lia; exact MU22) WM22
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 22) with (THR + 1968) by lia; exact PC22)) as FAM'.
    clear FAM PC22. rename FAM' into FAM. change (22 + 1) with 23 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU22; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU22) as MU'. clear MU MU22. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM22) as WM'. clear WM WM22. rename WM' into WM.
    clear MI21.

    destruct (FAM 23 ltac:(lia)) as [PC23 _]. unfold pcl_addr in PC23. rewrite THR_EQ in PC23.
    replace (THR + 208 + 80 * 23) with (THR + 2048) in PC23 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC23.
    eapply evt_cut; [eapply (ic_r_23 _ _ _ _ _ _ _ PC23); assumption|].
    clear PC23. intros ms23 PO. destruct PO as (y3_23 & y4_23 & y5_23 & m23 & -> & MU23 & WM23 & MI23 & PC23).
    pose proof (pcl_fam_step AL _ _ P 23 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 23) with (THR + 2048) by lia; exact MU23) WM23
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 23) with (THR + 2048) by lia; exact PC23)) as FAM'.
    clear FAM PC23. rename FAM' into FAM. change (23 + 1) with 24 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU23; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU23) as MU'. clear MU MU23. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM23) as WM'. clear WM WM23. rename WM' into WM.
    clear MI22.

    destruct (FAM 24 ltac:(lia)) as [PC24 _]. unfold pcl_addr in PC24. rewrite THR_EQ in PC24.
    replace (THR + 208 + 80 * 24) with (THR + 2128) in PC24 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC24.
    eapply evt_cut; [eapply (ic_r_24 _ _ _ _ _ _ _ PC24); assumption|].
    clear PC24. intros ms24 PO. destruct PO as (y3_24 & y4_24 & y5_24 & m24 & -> & MU24 & WM24 & MI24 & PC24).
    pose proof (pcl_fam_step AL _ _ P 24 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 24) with (THR + 2128) by lia; exact MU24) WM24
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 24) with (THR + 2128) by lia; exact PC24)) as FAM'.
    clear FAM PC24. rename FAM' into FAM. change (24 + 1) with 25 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU24; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU24) as MU'. clear MU MU24. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM24) as WM'. clear WM WM24. rename WM' into WM.
    clear MI23.

    destruct (FAM 25 ltac:(lia)) as [PC25 _]. unfold pcl_addr in PC25. rewrite THR_EQ in PC25.
    replace (THR + 208 + 80 * 25) with (THR + 2208) in PC25 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC25.
    eapply evt_cut; [eapply (ic_r_25 _ _ _ _ _ _ _ PC25); assumption|].
    clear PC25. intros ms25 PO. destruct PO as (y3_25 & y4_25 & y5_25 & m25 & -> & MU25 & WM25 & MI25 & PC25).
    pose proof (pcl_fam_step AL _ _ P 25 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 25) with (THR + 2208) by lia; exact MU25) WM25
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 25) with (THR + 2208) by lia; exact PC25)) as FAM'.
    clear FAM PC25. rename FAM' into FAM. change (25 + 1) with 26 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU25; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU25) as MU'. clear MU MU25. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM25) as WM'. clear WM WM25. rename WM' into WM.
    clear MI24.

    destruct (FAM 26 ltac:(lia)) as [PC26 _]. unfold pcl_addr in PC26. rewrite THR_EQ in PC26.
    replace (THR + 208 + 80 * 26) with (THR + 2288) in PC26 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC26.
    eapply evt_cut; [eapply (ic_r_26 _ _ _ _ _ _ _ PC26); assumption|].
    clear PC26. intros ms26 PO. destruct PO as (y3_26 & y4_26 & y5_26 & m26 & -> & MU26 & WM26 & MI26 & PC26).
    pose proof (pcl_fam_step AL _ _ P 26 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 26) with (THR + 2288) by lia; exact MU26) WM26
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 26) with (THR + 2288) by lia; exact PC26)) as FAM'.
    clear FAM PC26. rename FAM' into FAM. change (26 + 1) with 27 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU26; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU26) as MU'. clear MU MU26. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM26) as WM'. clear WM WM26. rename WM' into WM.
    clear MI25.

    destruct (FAM 27 ltac:(lia)) as [PC27 _]. unfold pcl_addr in PC27. rewrite THR_EQ in PC27.
    replace (THR + 208 + 80 * 27) with (THR + 2368) in PC27 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC27.
    eapply evt_cut; [eapply (ic_r_27 _ _ _ _ _ _ _ PC27); assumption|].
    clear PC27. intros ms27 PO. destruct PO as (y3_27 & y4_27 & y5_27 & m27 & -> & MU27 & WM27 & MI27 & PC27).
    pose proof (pcl_fam_step AL _ _ P 27 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 27) with (THR + 2368) by lia; exact MU27) WM27
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 27) with (THR + 2368) by lia; exact PC27)) as FAM'.
    clear FAM PC27. rename FAM' into FAM. change (27 + 1) with 28 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU27; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU27) as MU'. clear MU MU27. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM27) as WM'. clear WM WM27. rename WM' into WM.
    clear MI26.

    destruct (FAM 28 ltac:(lia)) as [PC28 _]. unfold pcl_addr in PC28. rewrite THR_EQ in PC28.
    replace (THR + 208 + 80 * 28) with (THR + 2448) in PC28 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC28.
    eapply evt_cut; [eapply (ic_r_28 _ _ _ _ _ _ _ PC28); assumption|].
    clear PC28. intros ms28 PO. destruct PO as (y3_28 & y4_28 & y5_28 & m28 & -> & MU28 & WM28 & MI28 & PC28).
    pose proof (pcl_fam_step AL _ _ P 28 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 28) with (THR + 2448) by lia; exact MU28) WM28
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 28) with (THR + 2448) by lia; exact PC28)) as FAM'.
    clear FAM PC28. rename FAM' into FAM. change (28 + 1) with 29 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU28; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU28) as MU'. clear MU MU28. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM28) as WM'. clear WM WM28. rename WM' into WM.
    clear MI27.

    destruct (FAM 29 ltac:(lia)) as [PC29 _]. unfold pcl_addr in PC29. rewrite THR_EQ in PC29.
    replace (THR + 208 + 80 * 29) with (THR + 2528) in PC29 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC29.
    eapply evt_cut; [eapply (ic_r_29 _ _ _ _ _ _ _ PC29); assumption|].
    clear PC29. intros ms29 PO. destruct PO as (y3_29 & y4_29 & y5_29 & m29 & -> & MU29 & WM29 & MI29 & PC29).
    pose proof (pcl_fam_step AL _ _ P 29 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 29) with (THR + 2528) by lia; exact MU29) WM29
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 29) with (THR + 2528) by lia; exact PC29)) as FAM'.
    clear FAM PC29. rename FAM' into FAM. change (29 + 1) with 30 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU29; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU29) as MU'. clear MU MU29. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM29) as WM'. clear WM WM29. rename WM' into WM.
    clear MI28.

    destruct (FAM 30 ltac:(lia)) as [PC30 _]. unfold pcl_addr in PC30. rewrite THR_EQ in PC30.
    replace (THR + 208 + 80 * 30) with (THR + 2608) in PC30 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC30.
    eapply evt_cut; [eapply (ic_r_30 _ _ _ _ _ _ _ PC30); assumption|].
    clear PC30. intros ms30 PO. destruct PO as (y3_30 & y4_30 & y5_30 & m30 & -> & MU30 & WM30 & MI30 & PC30).
    pose proof (pcl_fam_step AL _ _ P 30 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 30) with (THR + 2608) by lia; exact MU30) WM30
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 30) with (THR + 2608) by lia; exact PC30)) as FAM'.
    clear FAM PC30. rename FAM' into FAM. change (30 + 1) with 31 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU30; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU30) as MU'. clear MU MU30. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM30) as WM'. clear WM WM30. rename WM' into WM.
    clear MI29.

    destruct (FAM 31 ltac:(lia)) as [PC31 _]. unfold pcl_addr in PC31. rewrite THR_EQ in PC31.
    replace (THR + 208 + 80 * 31) with (THR + 2688) in PC31 by lia. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont] in PC31.
    eapply evt_cut; [eapply (ic_r_31 _ _ _ _ _ _ _ PC31); assumption|].
    clear PC31. intros ms31 PO. destruct PO as (y3_31 & y4_31 & y5_31 & m31 & -> & MU31 & WM31 & MI31 & PC31).
    pose proof (pcl_fam_step AL _ _ P 31 FAM ltac:(lia) ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 31) with (THR + 2688) by lia; exact MU31) WM31
                  ltac:(unfold pcl_addr; rewrite THR_EQ; replace (THR + 208 + 80 * 31) with (THR + 2688) by lia; exact PC31)) as FAM'.
    clear FAM PC31. rename FAM' into FAM. change (31 + 1) with 32 in FAM.
    apply (munch_weaken _ [(THR + 292, THR + 2704)]) in MU31; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_trans _ _ _ _ MU MU31) as MU'. clear MU MU31. rename MU' into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM31) as WM'. clear WM WM31. rename WM' into WM.
    clear MI30.
    apply evt_done. eexists _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI31|]. exact (pcl_fam_inited AL _ P FAM).
  Qed.
End IC.
