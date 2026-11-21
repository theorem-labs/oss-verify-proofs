(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZProg ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz Deflate RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require HarnessSmall ZApiInst ZTaint.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflateInitLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.HarnessSmall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZTaint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition spre (G : N -> Z -> Z) (po : Z) : deflate_state :=
  set_pending_out (s_fin (S5g 0%N 1%N 2%N 3%N 4%N (G 0%N) (G 1%N) (G 2%N) (G 3%N) (G 4%N) dinit_cs 1 15 8) 6 0 8) po.

Lemma RK0_set_po : forall s po, RK0 (set_pending_out s po) = RK0 s.
Proof. intros s po. destruct s. reflexivity. Qed.

Lemma dinit_state_eq : forall G po, LM (tr_init (RK0 (spre G po))) = dinit_of G.
Proof.
  intros G po. unfold spre. rewrite RK0_set_po. unfold dinit_of.
  apply (dFg_eq 0%N 1%N 2%N 3%N 4%N (G 0%N) (G 1%N) (G 2%N) (G 3%N) (G 4%N) dinit_cs 1 15 8 6 0 8).
Qed.

Lemma spre_facts : forall G po,
  deflateStateCheck (spre G po) = false /\ ds_wrap (spre G po) = 1 /\ ds_level (spre G po) = 6
  /\ ds_w_size (spre G po) = 32768 /\ ds_hash_size (spre G po) = 32768.
Proof. intros G po. repeat split; reflexivity. Qed.

Lemma spre_lens : forall G po, dlens (spre G po).
Proof. intros G po. constructor; reflexivity. Qed.

Lemma dz_init_scalars : zs_msg (dz_z zd_init) = MSG_NULL /\ zs_data_type (dz_z zd_init) = 2 /\ zs_adler (dz_z zd_init) = 1
  /\ zs_total_in (dz_z zd_init) = 0 /\ zs_total_out (dz_z zd_init) = 0.
Proof. unfold zd_init. cbn [dz_z]. rewrite dz0_of. repeat split; reflexivity. Qed.

Local Notation wz := (Z_to_bv 64).

Definition s_raw (G : N -> Z -> Z) : deflate_state := ds_of_oracle (G 0%N) 0%N dinit_cs.

Lemma spre_A_cells : forall G po L h1 h2 h3 h4 h5,
  dsA_cells L (spre G po) h1 h2 h3 h4 h5 =
  [C8 (wz (dl_S L)); C4 (wz INIT_STATE); CB 4 h1;
   C8 (wz (dl_Ab L)); C8 (wz 65536); C8 (wz (dl_Ab L + po));
   C8 (wz (init_u64 (G 0%N) 40 0)); C4 (wz 1); CB 4 h2; C8 (wz 0); C8 (wz (init_u64 (G 0%N) 64 0));
   C1 (Z_to_bv 8 8); CB 3 h3;
   C4 (wz (swrap32 (init_u32 (G 0%N) 76 0)));
   C4 (wz 32768); C4 (wz 15); C4 (wz 32767); CB 4 h4;
   C8 (wz (dl_Aw L)); C8 (wz (init_u64 (G 0%N) 104 0));
   C8 (wz (dl_Ap L)); C8 (wz (dl_Ah L)); C4 (wz (init_u32 (G 0%N) 128 0));
   C4 (wz 32768); C4 (wz 15); C4 (wz 32767); C4 (wz 5); CB 4 h5;
   C8 (wz (swrap64 (init_u64 (G 0%N) 152 0)));
   C4 (wz (init_u32 (G 0%N) 160 0));
   C4 (wz (init_u32 (G 0%N) 164 0));
   C4 (wz (swrap32 (init_u32 (G 0%N) 168 0)));
   C4 (wz (init_u32 (G 0%N) 172 0));
   C4 (wz (init_u32 (G 0%N) 176 0));
   C4 (wz (init_u32 (G 0%N) 180 0));
   C4 (wz (init_u32 (G 0%N) 184 0));
   C4 (wz (init_u32 (G 0%N) 188 0));
   C4 (wz (init_u32 (G 0%N) 192 0)); C4 (wz 6);
   C4 (wz 0); C4 (wz (init_u32 (G 0%N) 204 0));
   C4 (wz (swrap32 (init_u32 (G 0%N) 208 0)))].
Proof. intros. reflexivity. Qed.

Lemma spre_D_cells : forall G po L h0 h1 h2 h3 h4,
  dsD_cells L (spre G po) h0 h1 h2 h3 h4 =
  [CB 7 h0; C8 (wz (dl_Ab L + 16384));
   C4 (wz 16384); C4 (wz (init_u32 (G 0%N) 5900 0));
   C4 (wz 49149); CB 4 h1;
   C8 (wz (init_u64 (G 0%N) 5912 0));
   C8 (wz (init_u64 (G 0%N) 5920 0));
   C4 (wz (init_u32 (G 0%N) 5928 0));
   C4 (wz (init_u32 (G 0%N) 5932 0));
   C2 (wz (init_u16 (G 0%N) 5936 0)); CB 2 h2;
   C4 (wz (swrap32 (init_u32 (G 0%N) 5940 0)));
   CB 4 h3; C4 (wz 0);
   C8 (wz 0);
   CB 4 h4; C4 (wz 0)].
Proof. intros. reflexivity. Qed.

Lemma spre_Bi_cells : forall G po, dsBi_cells (spre G po) = dsBi_cells (s_raw G).
Proof. intros. reflexivity. Qed.
Lemma spre_C_cells : forall G po, dsC_cells (spre G po) = dsC_cells (s_raw G).
Proof. intros. reflexivity. Qed.
Lemma spre_lt : forall G po m L, dlt m L (s_raw G) -> dlt m L (spre G po).   Proof. intros G po m L H. exact H. Qed.
Lemma spre_dt : forall G po m L, ddt m L (s_raw G) -> ddt m L (spre G po).   Proof. intros G po m L H. exact H. Qed.
Lemma spre_bt : forall G po m L, dbt m L (s_raw G) -> dbt m L (spre G po).   Proof. intros G po m L H. exact H. Qed.
Lemma spre_blc : forall G po m L, dblc m L (s_raw G) -> dblc m L (spre G po). Proof. intros G po m L H. exact H. Qed.
Lemma spre_heap : forall G po m L, dheap m L (s_raw G) -> dheap m L (spre G po). Proof. intros G po m L H. exact H. Qed.
Lemma spre_dep : forall G po m L, ddep m L (s_raw G) -> ddep m L (spre G po). Proof. intros G po m L H. exact H. Qed.

Lemma spre_win : forall G po m L, u8arr psegs m (dl_Aw L) (av8 (blk_bytes (G 1%N) 65536) 65536) -> dwin m L (spre G po).
Proof. intros G po m L H. exact H. Qed.
Lemma spre_prev : forall G po m L, u16arr psegs m (dl_Ap L) (av16 (blk_ush (G 2%N) 32768) 32768) -> dprev m L (spre G po).
Proof. intros G po m L H. exact H. Qed.
Lemma spre_head : forall G po m L, u16arr psegs m (dl_Ah L) (av16 (blk_ush (G 3%N) 32768) 32768) -> dhead m L (spre G po).
Proof. intros G po m L H. exact H. Qed.
Lemma spre_pend : forall G po m L, u8arr psegs m (dl_Ab L) (av8 (blk_bytes (G 4%N) 65536) 65536) -> dpend m L (spre G po).
Proof. intros G po m L H. exact H. Qed.
