(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G Require Import GlueKit.

Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_reshape : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells segs m A cs'.
Proof. intros segs m A cs cs' [[W B] S] W' B' S'. split; [split; [exact W'| rewrite B'; exact B]| rewrite S'; exact S]. Qed.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_app2 : forall (m : mem) A cs1 cs2 B, rw_cells asegs m A cs1 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells asegs m B cs2 ->
  rw_cells asegs m A (cs1 ++ cs2).
Proof. intros m A cs1 cs2 B H1 -> H2. apply (proj2 (rw_cells_app asegs m A cs1 cs2)). split; assumption. Qed.

Lemma bytes_eq_unsigned : forall l l' : list byte, map bv_unsigned l = map bv_unsigned l' -> l = l'.
Proof.
  induction l as [|a l IH]; destruct l' as [|b l']; cbn; intros H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Ltac reshape8 H := eapply rw_cells_reshape; [exact H | cbn; repeat split; reflexivity | apply bytes_eq_unsigned; vm_compute; reflexivity | reflexivity].

Lemma icpt_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> Shadow.icpt_env asegs m.
Proof.
  intros V m HM.
  unfold icpt_env, env_shadow, env_layout, env_inited, env_ric, env_real_mem, env_cf, env_flags, env_real_str, env_real_io, env_ckpf, env_aflags, env_real_lib, env_real_lib2, env_got_rms, env_got_rmem, env_real_cmp.

  split. { split. { aimg V m HM 0xaad30 [C8 (Z_to_bv 64 0xb4538)] H. exact H. }
           mf V m HM (MCell (ZLit 738616) 8 (ZLit 2147450880)) H. exact H. }

  split. { split. { aimg V m HM 0xaad38 [C8 (Z_to_bv 64 0xb5228); C8 (Z_to_bv 64 0xb5230); C8 (Z_to_bv 64 0xb5220)] H. exact H. }
           mf V m HM (MCell (ZLit 741920) 8 (ZLit 140737488355327)) H1.
           aimg V m HM 0xb5228 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H2.
           exact (rw_cells_app2 m _ _ _ 741928 H1 eq_refl H2). }

  split. { mf V m HM (MCell (ZLit 741912) 1 (ZLit 1)) H1. mf V m HM (MCell (ZLit 741913) 1 (ZLit 1)) H2.
           exact (rw_cells_app2 m _ _ _ 741913 H1 eq_refl H2). }

  split. { aimg V m HM 0xab898 [C8 (Z_to_bv 64 0xb5219)] H. exact H. }

  split. { aimg V m HM 0xacbd8 [C8 (Z_to_bv 64 0xa2a7c); C8 (Z_to_bv 64 0xa2e80)] H. exact H. }

  split. { aimg V m HM 0xaad20 [C8 (Z_to_bv 64 0x146068); C8 (Z_to_bv 64 0xb1d38)] H. exact H. }

  split. { mf V m HM (MCell (ZLit 1335640) 8 (ZLit 72339073309605888)) H1. mf V m HM (MCell (ZLit 1335648) 8 (ZLit 72340172838076673)) H2.
           pose proof (rw_cells_app2 m _ _ _ 1335648 H1 eq_refl H2) as H. reshape8 H. }

  split. { split. { aimg V m HM 0xaca48 [C8 (Z_to_bv 64 0xa30cc)] H. exact H. }
           split. { aimg V m HM 0xaca80 [C8 (Z_to_bv 64 0xa2980)] H. exact H. }
           aimg V m HM 0xacb88 [C8 (Z_to_bv 64 0xa342c)] H. exact H. }

  split. { split. { aimg V m HM 0xaca90 [C8 (Z_to_bv 64 0xa96e8); C8 (Z_to_bv 64 0x9bd20)] H. exact H. }
           aimg V m HM 0xacac8 [C8 (Z_to_bv 64 0xa228c); C8 (Z_to_bv 64 0x9bfa8)] H. exact H. }

  split. { mf V m HM (MCell (ZLit 1335480) 8 (ZLit 4294967296)) H. reshape8 H. }

  split. { mf V m HM (MCell (ZLit 728400) 8 (ZLit 72340168526266369)) H. reshape8 H. }

  split. { split. { aimg V m HM 0xaca68 [C8 (Z_to_bv 64 0xa3470)] H. exact H. }
           split. { aimg V m HM 0xacab8 [C8 (Z_to_bv 64 0xa2450); C8 (Z_to_bv 64 0x9e9e0)] H. exact H. }
           split. { aimg V m HM 0xacae8 [C8 (Z_to_bv 64 0x9a630)] H. exact H. }
           aimg V m HM 0xacbb0 [C8 (Z_to_bv 64 0xa2760); C8 (Z_to_bv 64 0xa28c8); C8 (Z_to_bv 64 0xa2590)] H. exact H. }

  split. { aimg V m HM 0xacba8 [C8 (Z_to_bv 64 0xa32f4)] H. exact H. }

  split. { aimg V m HM 0xaad50 [C8 (Z_to_bv 64 0xacbe0)] H. exact H. }
  split. { aimg V m HM 0xaad58 [C8 (Z_to_bv 64 0xacbd8)] H. exact H. }

  split. { aimg V m HM 0xaca70 [C8 (Z_to_bv 64 0xa2f78)] H. exact H. }
  aimg V m HM 0xaca78 [C8 (Z_to_bv 64 0xa2a4c)] H. exact H.
Qed.
