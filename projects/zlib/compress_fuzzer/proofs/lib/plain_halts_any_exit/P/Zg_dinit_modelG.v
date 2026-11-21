(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dinit_model.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz Deflate RefDeflateInitLib RefDeflSafeI5b HarnessSmall ZApiInst ZTaint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition dinitG_of (G : N -> Z -> Z) (lv : Z) : deflate_state :=
  dFg 0%N 1%N 2%N 3%N 4%N (G 0%N) (G 1%N) (G 2%N) (G 3%N) (G 4%N) dinit_cs 1 15 8 lv 0 8.

Definition zsG : zstrm := mkZS 0 0 1 2 MSG_NULL.

Definition spreG (G : N -> Z -> Z) (po : Z) (lv : Z) : deflate_state :=
  set_pending_out (s_fin (S5g 0%N 1%N 2%N 3%N 4%N (G 0%N) (G 1%N) (G 2%N) (G 3%N) (G 4%N) dinit_cs 1 15 8) lv 0 8) po.

Lemma dinitG_state_eq : forall G po lv, LM (tr_init (RK0 (spreG G po lv))) = dinitG_of G lv.
Proof.
  intros G po lv. unfold spreG. rewrite RK0_set_po. unfold dinitG_of.
  apply (dFg_eq 0%N 1%N 2%N 3%N 4%N (G 0%N) (G 1%N) (G 2%N) (G 3%N) (G 4%N) dinit_cs 1 15 8 lv 0 8).
Qed.

Lemma spreG_facts : forall G po lv,
  deflateStateCheck (spreG G po lv) = false /\ ds_wrap (spreG G po lv) = 1 /\ ds_level (spreG G po lv) = lv
  /\ ds_w_size (spreG G po lv) = 32768 /\ ds_hash_size (spreG G po lv) = 32768.
Proof. intros G po lv. repeat split; reflexivity. Qed.

Lemma spreG_lens : forall G po lv, dlens (spreG G po lv).
Proof. intros G po lv. constructor; reflexivity. Qed.

Local Notation wz := (Z_to_bv 64).

Lemma spreG_A_cells : forall G po lv L h1 h2 h3 h4 h5,
  dsA_cells L (spreG G po lv) h1 h2 h3 h4 h5 =
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
   C4 (wz (init_u32 (G 0%N) 192 0)); C4 (wz lv);
   C4 (wz 0); C4 (wz (init_u32 (G 0%N) 204 0));
   C4 (wz (swrap32 (init_u32 (G 0%N) 208 0)))].
Proof. intros. reflexivity. Qed.

Lemma spreG_D_cells : forall G po lv L h0 h1 h2 h3 h4,
  dsD_cells L (spreG G po lv) h0 h1 h2 h3 h4 =
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

Lemma spreG_Bi_cells : forall G po lv, dsBi_cells (spreG G po lv) = dsBi_cells (s_raw G).
Proof. intros. reflexivity. Qed.
Lemma spreG_C_cells : forall G po lv, dsC_cells (spreG G po lv) = dsC_cells (s_raw G).
Proof. intros. reflexivity. Qed.
Lemma spreG_lt : forall G po lv m L, dlt m L (s_raw G) -> dlt m L (spreG G po lv).   Proof. intros G po lv m L H. exact H. Qed.
Lemma spreG_dt : forall G po lv m L, ddt m L (s_raw G) -> ddt m L (spreG G po lv).   Proof. intros G po lv m L H. exact H. Qed.
Lemma spreG_bt : forall G po lv m L, dbt m L (s_raw G) -> dbt m L (spreG G po lv).   Proof. intros G po lv m L H. exact H. Qed.
Lemma spreG_blc : forall G po lv m L, dblc m L (s_raw G) -> dblc m L (spreG G po lv). Proof. intros G po lv m L H. exact H. Qed.
Lemma spreG_heap : forall G po lv m L, dheap m L (s_raw G) -> dheap m L (spreG G po lv). Proof. intros G po lv m L H. exact H. Qed.
Lemma spreG_dep : forall G po lv m L, ddep m L (s_raw G) -> ddep m L (spreG G po lv). Proof. intros G po lv m L H. exact H. Qed.

Lemma spreG_win : forall G po lv m L, u8arr psegs m (dl_Aw L) (av8 (blk_bytes (G 1%N) 65536) 65536) -> dwin m L (spreG G po lv).
Proof. intros G po lv m L H. exact H. Qed.
Lemma spreG_prev : forall G po lv m L, u16arr psegs m (dl_Ap L) (av16 (blk_ush (G 2%N) 32768) 32768) -> dprev m L (spreG G po lv).
Proof. intros G po lv m L H. exact H. Qed.
Lemma spreG_head : forall G po lv m L, u16arr psegs m (dl_Ah L) (av16 (blk_ush (G 3%N) 32768) 32768) -> dhead m L (spreG G po lv).
Proof. intros G po lv m L H. exact H. Qed.
Lemma spreG_pend : forall G po lv m L, u8arr psegs m (dl_Ab L) (av8 (blk_bytes (G 4%N) 65536) 65536) -> dpend m L (spreG G po lv).
Proof. intros G po lv m L H. exact H. Qed.
