(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz Deflate. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateInitLib RefDeflSafeI5b. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import HarnessSmall HarnessLarge ZApiInst ZApiInstL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import ZTaint ZTaintL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition spre9 (G : N -> Z -> Z) (po : Z) : deflate_state :=
  set_pending_out (s_fin (S5g 0%N 1%N 2%N 3%N 4%N (G 0%N) (G 1%N) (G 2%N) (G 3%N) (G 4%N) dinit_cs 1 15 8) 9 0 8) po.

Lemma RK0_set_po9 : forall s po, RK0 (set_pending_out s po) = RK0 s.
Proof. intros s po. destruct s. reflexivity. Qed.

Lemma dinit9_state_eq : forall G po, LM (tr_init (RK0 (spre9 G po))) = dinit9_of G.
Proof.
  intros G po. unfold spre9. rewrite RK0_set_po9. unfold dinit9_of.
  apply (dFg_eq 0%N 1%N 2%N 3%N 4%N (G 0%N) (G 1%N) (G 2%N) (G 3%N) (G 4%N) dinit_cs 1 15 8 9 0 8).
Qed.

Lemma spre9_facts : forall G po,
  deflateStateCheck (spre9 G po) = false /\ ds_wrap (spre9 G po) = 1 /\ ds_level (spre9 G po) = 9
  /\ ds_w_size (spre9 G po) = 32768 /\ ds_hash_size (spre9 G po) = 32768.
Proof. intros G po. repeat split; reflexivity. Qed.

Lemma spre9_lens : forall G po, dlens (spre9 G po).
Proof. intros G po. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Lemma dz9_init_scalars : zs_msg (dz_z zdl_init9) = MSG_NULL /\ zs_data_type (dz_z zdl_init9) = 2 /\ zs_adler (dz_z zdl_init9) = 1
  /\ zs_total_in (dz_z zdl_init9) = 0 /\ zs_total_out (dz_z zdl_init9) = 0.
Proof. unfold zdl_init9. cbn [dz_z]. rewrite dz9_of. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition s_raw9 (G : N -> Z -> Z) : deflate_state := ds_of_oracle (G 0%N) 0%N dinit_cs.

Lemma spre9_A_cells : forall G po L h1 h2 h3 h4 h5,
  dsA_cells L (spre9 G po) h1 h2 h3 h4 h5 =
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
   C4 (wz (init_u32 (G 0%N) 192 0)); C4 (wz 9);
   C4 (wz 0); C4 (wz (init_u32 (G 0%N) 204 0));
   C4 (wz (swrap32 (init_u32 (G 0%N) 208 0)))].
Proof. intros. reflexivity. Qed.

Lemma spre9_D_cells : forall G po L h0 h1 h2 h3 h4,
  dsD_cells L (spre9 G po) h0 h1 h2 h3 h4 =
  [CB 7 h0; C8 (wz (dl_Ab L + 16384));
   C4 (wz 16384); C4 (wz (init_u32 (G 0%N) 5900 0));
   C4 (wz 49149); CB 4 h1;
   C8 (wz (init_u64 (G 0%N) 5912 0));
   C8 (wz (init_u64 (G 0%N) 5920 0));
   C4 (wz (init_u32 (G 0%N) 5928 0));
   C4 (wz (init_u32 (G 0%N) 5932 0));
   C2 (wz (init_u16 (G 0%N) 5936 0)); CB 2 h2;
   C4 (wz (swrap32 (init_u32 (G 0%N) 5940 0)));
   CB 4 h3; C4 (wz 0); C8 (wz 0); CB 4 h4; C4 (wz 0)].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma spre9_Bi_cells : forall G po, dsBi_cells (spre9 G po) = dsBi_cells (s_raw9 G).
Proof. intros. reflexivity. Qed.
Lemma spre9_C_cells : forall G po, dsC_cells (spre9 G po) = dsC_cells (s_raw9 G).
Proof. intros. reflexivity. Qed.
Lemma spre9_lt : forall G po m L, dlt m L (s_raw9 G) -> dlt m L (spre9 G po).   Proof. intros G po m L H. exact H. Qed.
Lemma spre9_dt : forall G po m L, ddt m L (s_raw9 G) -> ddt m L (spre9 G po).   Proof. intros G po m L H. exact H. Qed.
Lemma spre9_bt : forall G po m L, dbt m L (s_raw9 G) -> dbt m L (spre9 G po).   Proof. intros G po m L H. exact H. Qed.
Lemma spre9_blc : forall G po m L, dblc m L (s_raw9 G) -> dblc m L (spre9 G po). Proof. intros G po m L H. exact H. Qed.
Lemma spre9_heap : forall G po m L, dheap m L (s_raw9 G) -> dheap m L (spre9 G po). Proof. intros G po m L H. exact H. Qed.
Lemma spre9_dep : forall G po m L, ddep m L (s_raw9 G) -> ddep m L (spre9 G po). Proof. intros G po m L H. exact H. Qed.

(* [comment removed for export] *)
Lemma spre9_win : forall G po m L, u8arr psegs m (dl_Aw L) (av8 (blk_bytes (G 1%N) 65536) 65536) -> dwin m L (spre9 G po).
Proof. intros G po m L H. exact H. Qed.
Lemma spre9_prev : forall G po m L, u16arr psegs m (dl_Ap L) (av16 (blk_ush (G 2%N) 32768) 32768) -> dprev m L (spre9 G po).
Proof. intros G po m L H. exact H. Qed.
Lemma spre9_head : forall G po m L, u16arr psegs m (dl_Ah L) (av16 (blk_ush (G 3%N) 32768) 32768) -> dhead m L (spre9 G po).
Proof. intros G po m L H. exact H. Qed.
Lemma spre9_pend : forall G po m L, u8arr psegs m (dl_Ab L) (av8 (blk_bytes (G 4%N) 65536) 65536) -> dpend m L (spre9 G po).
Proof. intros G po m L H. exact H. Qed.
