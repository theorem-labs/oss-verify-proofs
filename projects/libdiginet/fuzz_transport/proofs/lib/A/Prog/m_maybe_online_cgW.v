(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 678 of its 962 lines of code are new or changed and 855 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcHead.v, with its module paths and module names changed; 1104 of its 1184 lines of code are new or changed and 882 lines of the source are left out. *)
(* m_maybe_online: Theorem transport_m_maybe_online_cg_holds, the statement transport_m_maybe_online_cg_holds_stmt of
   lib/A/Prog/m_maybe_online_cg.v: the machine walk of m_maybe_online on fuzz_transport.asan at 0x850f0 (284 bytes,
   frame 16), with m_set (fuzz_transport.c:196-207) inlined.

   The walk is a G-form walk: it holds the caller's journal ajournal_gx G_HARNESS 0 [] (lib/A/W_journalG.v) from the
   entry to the return, and the runs are the symbolic runs of lib/A/Prog/PaShadow.v taken over that journal
   (lib/A/Prog/TransportGRunA.v paj_run_x). The function calls nothing, so there is no call step; its stores into M
   and OW are allowed by the run's write right awr_ok_x (bytes of G).

   The world is read as symbolic DATA. The walk's valuation carries the world byte list Bw as data block 0, and the
   five ranges of G the code reads or writes are regions whose chunk is CData 0 <world offset> <n> at the matching
   image base (TWorldA.v TMAP_A): M.state .. M.e1_us (world 12, 12 bytes at TA_M + 12), M.last_rx (world 32, 8
   bytes), M.next_ka (world 48, 8 bytes), g_cfg.keepalive_ms (world 65048, 4 bytes at the listing's object A_OBJ 30 =
   TA_g_cfg + 24) and OW.n (world 65312, 4 bytes at TA_OW). A load of one of those fields is then the model's
   accessor of Bw (mo_d_* below), so every branch is decided by the model premise m_maybe_online_m Bw = Some (Bw', tt)
   through the model lemmas mo_model_* below.

   The paths (each run stops at a branch; mo_branch splits it):
     run 1 (+0x00 .. +0x18)   the frame, the save of ra, a2 = &M, M.state and `bne a0, a1` at +0x18;
     path A1 (M.state <> 1)   the epilogue at +0xdc: the world is unchanged (mo_model_keep);
     run 2 (+0x1c .. +0x20)   M.e2_acked and `beqz` at +0x20;      path A2 (M.e2_acked = 0): as A1;
     run 3 (+0x24 .. +0x28)   M.e1_us and `beqz` at +0x28;         path A3 (M.e1_us = 0): as A1;
     run 4 (+0x2c .. +0x64)   M.last_rx, g_cfg.keepalive_ms, the shadow base through its GOT word, &OW, OW.n, the
                              8-byte store of keepalive_ms * 1000 + M.last_rx at M + 48 (:240), `blt a0, a4` at +0x64;
     path B (15 < OW.n)       +0xcc: the 4-byte stores of OW.n + 1 at OW + 0 and of 2 at M + 12, then the epilogue;
     path C(n) (0 <= n <= 15) the walk pins OW.n to each of its 16 values (the branch bounds it above, the model
                              premise forbids a negative index) and adds the region of OW.t[n] (12 bytes at
                              OW + 4 + 12n); the three checked 4-byte stores at OW + 4 + 12n, + 8 + 12n, + 12 + 12n
                              (:201-203), then OW.n + 1 and M.state = 2, then the epilogue.
   The instrumented check of each of those stores (the shadow byte of the store address, then the slow path's
   `andi` / `addi` / `blt`) is decided by the run's shadow entry over OW's whole payload [TA_OW, TA_OW + 304)
   (mo_shok, from the premise trans_ow_cells B of m_lost_cg.v: the shadow of OW's 38 granules is 0), so no error
   path (errpath_store4) is reached.

   The post (mo_close): transport_cg_post over G_HARNESS: the journal at the return, the callee-saved registers,
   acall_kept_g by TransportGCg.v dk_kept_step_g over the bytes the call may change (its stack window and
   monline_wr Bw), and the world relation at the model's world. The model lemmas give that world in closed form (a
   nested upd of Bw), and the chain mo_wstep transports the relation through it with TWorldG.v tw_write, one store
   at a time, over the reader mo_rdm (the final memory on the bytes written so far, the entry memory elsewhere). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s YFen.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f YK00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg m_maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0 TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module YO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YO0f.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK00.

(* ------------------------------------------------------------------ *)
(* Bit-vector facts about the branch conditions                        *)
(* ------------------------------------------------------------------ *)

Lemma mo_signed_int : forall x, -2^31 <= x < 2^31 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. destruct (Z_le_gt_dec 0 x) as [N|N].
  - apply YKK.bv_signed_small. lia.
  - replace x with (- (- x)) by lia. apply YKK.bv_signed_neg. lia.
Qed.

(* The unsigned image of a 32-bit signed value decides an equality with a small non-negative literal. *)
Lemma mo_mod_eqb : forall x y, -2^31 <= x < 2^31 -> 0 <= y < 2^31 -> (x mod 2 ^ 64 =? y) = (x =? y).
Proof.
  intros x y Hx Hy. destruct (Z_le_gt_dec 0 x) as [N|N].
  - rewrite (Z.mod_small x (2^64)) by lia. reflexivity.
  - assert (Hm : x mod 2^64 = x + 2^64).
    { rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. ring. }
    rewrite Hm. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
Qed.

Lemma mo_br_slt : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !mo_signed_int by assumption. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The model: what m_maybe_online_m Bw is on each path                 *)
(* ------------------------------------------------------------------ *)

(* The value the code stores at M.next_ka (:240): keepalive_ms * 1000 + last_rx, in 64 bits. *)
Definition MO_KA (Bw : list byte) : Z := TS0.u64 (TW.M_last_rx Bw + TCB.h_ms_m (TW.Cfg_keepalive_ms Bw)).

Lemma mo_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

(* The next_ka store (8 bytes at world offset 48) leaves M.state and OW.n alone. *)
Lemma mo_state_ka : forall (B0 : list byte) v, length B0 = Z.to_nat TW.W_LEN ->
  TW.M_state (TW.set_M_next_ka B0 v) = TW.M_state B0.
Proof.
  intros B0 v L. assert (LZ : Z.of_nat (length B0) = TW.W_LEN) by (rewrite L; reflexivity).
  unfold TW.M_state, TW.set_M_next_ka, TW.A_M_state, TW.A_M_next_ka, TW.OFF_M, TW.W_LEN in *.
  rewrite TWL.s32_at_upd_out; [reflexivity | lia | lia | rewrite TWL.length_put; lia | rewrite TWL.length_put; lia].
Qed.

Lemma mo_n_ka : forall (B0 : list byte) v, length B0 = Z.to_nat TW.W_LEN ->
  TW.OW_n (TW.set_M_next_ka B0 v) = TW.OW_n B0.
Proof.
  intros B0 v L. assert (LZ : Z.of_nat (length B0) = TW.W_LEN) by (rewrite L; reflexivity).
  unfold TW.OW_n, TW.set_M_next_ka, TW.A_OW_n, TW.A_M_next_ka, TW.OFF_OW, TW.OFF_M, TW.W_LEN in *.
  rewrite TWL.s32_at_upd_out; [reflexivity | lia | lia | rewrite TWL.length_put; lia | rewrite TWL.length_put; lia].
Qed.

(* Path A: one of the three tests of :239 fails, so the model keeps the world. *)
Lemma mo_model_keep : forall Bw Bw',
  (TW.M_state Bw <> TCB.S_WAKING \/ TW.M_e2_acked Bw = 0 \/ TW.M_e1_us Bw = 0) ->
  TCB.m_maybe_online_m Bw = Some (Bw', tt) -> Bw' = Bw.
Proof.
  intros Bw Bw' Hc Hm. unfold TCB.m_maybe_online_m, TCB.truth in Hm.
  replace ((TW.M_state Bw =? TCB.S_WAKING) && negb (TW.M_e2_acked Bw =? 0) && negb (TW.M_e1_us Bw =? 0))%bool
    with false in Hm.
  - exact (mo_some_inv _ _ Hm).
  - symmetry. destruct Hc as [H | [H | H]].
    + replace (TW.M_state Bw =? TCB.S_WAKING) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity.
    + rewrite H, Z.eqb_refl. cbn [negb]. rewrite andb_false_r, andb_false_l. reflexivity.
    + rewrite H, Z.eqb_refl. cbn [negb]. rewrite andb_false_r. reflexivity.
Qed.

(* The three tests of :239 hold: the model runs m_set on the world with next_ka set. *)
Lemma mo_model_set : forall Bw Bw',
  TW.M_state Bw = TCB.S_WAKING -> TW.M_e2_acked Bw <> 0 -> TW.M_e1_us Bw <> 0 ->
  TCB.m_maybe_online_m Bw = Some (Bw', tt) ->
  TCB.m_set_m (TW.set_M_next_ka Bw (MO_KA Bw)) TCB.S_ONLINE TCB.R_ONLINE = Some (Bw', tt).
Proof.
  intros Bw Bw' H1 H2 H3 Hm. unfold TCB.m_maybe_online_m, TCB.truth in Hm.
  rewrite H1 in Hm. rewrite Z.eqb_refl in Hm.
  replace (TW.M_e2_acked Bw =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; exact H2).
  replace (TW.M_e1_us Bw =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; exact H3).
  cbn [negb andb] in Hm. cbv beta iota in Hm. exact Hm.
Qed.

(* Path B: OW.n is above the log's last slot, so m_set writes only OW.n and M.state. *)
Lemma mo_model_B : forall Bw Bw', length Bw = Z.to_nat TW.W_LEN ->
  TW.M_state Bw = TCB.S_WAKING -> TW.M_e2_acked Bw <> 0 -> TW.M_e1_us Bw <> 0 ->
  TCB.TRANS_MAX <= TW.OW_n Bw ->
  TCB.m_maybe_online_m Bw = Some (Bw', tt) ->
  TW.OW_n Bw < TCB.INT_MAX /\
  Bw' = TW.set_M_state (TW.set_OW_n (TW.set_M_next_ka Bw (MO_KA Bw)) (TW.OW_n Bw + 1)) TCB.S_ONLINE.
Proof.
  intros Bw Bw' HL H1 H2 H3 Hn Hm.
  pose proof (mo_model_set Bw Bw' H1 H2 H3 Hm) as Hs.
  unfold TCB.m_set_m in Hs. rewrite (mo_state_ka Bw _ HL), (mo_n_ka Bw _ HL), H1 in Hs.
  replace (TCB.S_WAKING =? TCB.S_ONLINE) with false in Hs by reflexivity.
  cbv beta iota zeta in Hs.
  replace (TW.OW_n Bw <? TCB.TRANS_MAX) with false in Hs by (symmetry; apply Z.ltb_ge; exact Hn).
  cbv beta iota zeta in Hs. unfold TCB.int_inc in Hs.
  assert (HR : -2 ^ 31 <= TW.OW_n Bw < 2 ^ 31) by (unfold TW.OW_n; apply TWL.s32_range).
  destruct (TW.OW_n Bw =? TCB.INT_MAX) eqn:EI.
  - cbv beta iota zeta in Hs. discriminate Hs.
  - cbv beta iota zeta in Hs. apply Z.eqb_neq in EI.
    split; [unfold TCB.INT_MAX in *; lia|]. exact (mo_some_inv _ _ Hs).
Qed.

(* Path C: 0 <= OW.n <= 15 (the model forbids a negative index), and m_set writes the slot too. *)
Lemma mo_model_C : forall Bw Bw', length Bw = Z.to_nat TW.W_LEN ->
  TW.M_state Bw = TCB.S_WAKING -> TW.M_e2_acked Bw <> 0 -> TW.M_e1_us Bw <> 0 ->
  TW.OW_n Bw < TCB.TRANS_MAX ->
  TCB.m_maybe_online_m Bw = Some (Bw', tt) ->
  0 <= TW.OW_n Bw /\
  Bw' = TW.set_M_state (TW.set_OW_n
          (TW.set_OW_t_reason (TW.set_OW_t_old (TW.set_OW_t_state (TW.set_M_next_ka Bw (MO_KA Bw))
             (TW.OW_n Bw) TCB.S_ONLINE) (TW.OW_n Bw) TCB.S_WAKING) (TW.OW_n Bw) TCB.R_ONLINE)
          (TW.OW_n Bw + 1)) TCB.S_ONLINE.
Proof.
  intros Bw Bw' HL H1 H2 H3 Hn Hm.
  pose proof (mo_model_set Bw Bw' H1 H2 H3 Hm) as Hs.
  unfold TCB.m_set_m in Hs. rewrite (mo_state_ka Bw _ HL), (mo_n_ka Bw _ HL), H1 in Hs.
  replace (TCB.S_WAKING =? TCB.S_ONLINE) with false in Hs by reflexivity.
  cbv beta iota zeta in Hs.
  replace (TW.OW_n Bw <? TCB.TRANS_MAX) with true in Hs by (symmetry; apply Z.ltb_lt; exact Hn).
  cbv beta iota zeta in Hs.
  assert (H0 : 0 <= TW.OW_n Bw).
  { destruct (Z_lt_le_dec (TW.OW_n Bw) 0) as [Hlt | Hge]; [exfalso | exact Hge].
    replace (TW.OW_n Bw <? 0) with true in Hs by (symmetry; apply Z.ltb_lt; exact Hlt).
    cbv beta iota zeta in Hs. discriminate Hs. }
  split; [exact H0|].
  replace (TW.OW_n Bw <? 0) with false in Hs by (symmetry; apply Z.ltb_ge; exact H0).
  cbv beta iota zeta in Hs. unfold TCB.int_inc in Hs.
  replace (TW.OW_n Bw =? TCB.INT_MAX) with false in Hs
    by (symmetry; apply Z.eqb_neq; unfold TCB.TRANS_MAX, TCB.INT_MAX in *; lia).
  cbv beta iota zeta in Hs. exact (mo_some_inv _ _ Hs).
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* The ranges of G the code reads or writes, as regions over the world data block 0: each chunk is the world's own
   bytes at the matching world offset. Writable: M.state (the 4 bytes at 12), M.next_ka, OW.n, and the slot
   OW.t[n] (mo_rT, added once the walk has pinned n). *)
Definition mo_rM1 : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 12 24 12 16 [YP09.mkChunk 12 (CData 0%nat 12 12)].
Definition mo_rM2 : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 32 40 0 0 [YP09.mkChunk 32 (CData 0%nat 32 8)].
Definition mo_rM3 : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 48 56 48 56 [YP09.mkChunk 48 (CData 0%nat 48 8)].
Definition mo_rK : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 30)) 0 4 0 0 [YP09.mkChunk 0 (CData 0%nat TW.A_Cfg_keepalive_ms 4)].
Definition mo_rO : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 0 4 0 4 [YP09.mkChunk 0 (CData 0%nat TW.A_OW_n 4)].
Definition mo_rT (n : Z) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 12)) (4 + 12 * n) (16 + 12 * n) (4 + 12 * n) (16 + 12 * n) [].
Definition mo_regions : smem :=
  [stack_region MONLINE_FRAME; got_regionP; bcell_regionP 32; mo_rM1; mo_rM2; mo_rM3; mo_rK; mo_rO].
Definition mo_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 8, mkAF TA_M TA_M 4); (A_OBJ 12, mkAF TA_OW TA_OW 4)] [] [].
Definition ss_mo : sstate := mkSS AF_m_maybe_online sr_atoms mo_regions None mo_facts.
(* The shadow entry of OW's whole payload, and the shadow base of the token engine. *)
Definition MO_SH : list shent := [mkSHE (A_OBJ 12) 0 TW.SZ_OW].
Definition MO_Bx : sv := SOff 32 0.

(* The windows the walk's regions carry: the call's stack window and the four written ranges of G. *)
Definition mo_win (sp a : Z) : Prop :=
  (sp - MONLINE_STK <= a < sp) \/ (TA_M + 12 <= a < TA_M + 16) \/ (TA_M + 48 <= a < TA_M + 56) \/
  (TA_OW <= a < TA_OW + 4).
Definition mo_winT (sp n a : Z) : Prop := mo_win sp a \/ (TA_OW + 4 + 12 * n <= a < TA_OW + 16 + 12 * n).

(* The value of register r in the machine state of a symbolic state HS (E2's scfg_reg). *)
Ltac mo_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mo_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs (E2's scfg_win). *)
Ltac mo_win_tac Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section mow. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma mo_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 12) = TA_OW /\ VAL (A_OBJ 30) = TA_g_cfg + 24 /\
  BASE + AF_m_maybe_online = transport_sigma TS_m_maybe_online.
Proof. vm_compute. repeat split. Qed.

(* ---- the valuation: the registers, the shadow base, and the world as data block 0 ---- *)

Definition mo_E (regs : bvmap 5 word) (Bw : list byte) : env :=
  edset (Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF])) 0%nat Bw.

Lemma mo_ew : forall regs Bw n,
  ew (mo_E regs Bw) n = ew (Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF])) n.
Proof. reflexivity. Qed.

Lemma mo_ed : forall regs Bw, ed (mo_E regs Bw) 0%nat = Bw.
Proof. intros regs Bw. unfold mo_E, edset. cbn [ed]. reflexivity. Qed.

Lemma mo_img_env : forall regs Bw, img_env VAL A_LIM (mo_E regs Bw).
Proof. intros regs Bw a Ha. exact (Eimg_env (Ereg regs [w64 SHADOW_OFF]) a Ha). Qed.

Lemma mo_regs_ok : forall regs Bw, regs_ok (mo_E regs Bw) sr_atoms regs.
Proof.
  intros regs Bw.
  apply (regs_ok_agree_on (fun _ => true) (Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]))
          (mo_E regs Bw) sr_atoms regs).
  - intros n _. rewrite mo_ew. reflexivity.
  - vm_compute. reflexivity.
  - apply regs_ok_Eimg_Ereg.
Qed.

(* ---- the denotation of a load from the world data block ---- *)

Lemma mo_data_u4 : forall regs Bw k,
  sv_denot (mo_E regs Bw) (SData 0%nat k 4) = Z_to_bv 64 (TW.u_at Bw k 4%nat).
Proof.
  intros regs Bw k. cbn [sv_denot]. f_equal.
  all: unfold data_word, TW.u_at, TW.sub; rewrite mo_ed; reflexivity.
Qed.

Lemma mo_data_u8 : forall regs Bw k,
  sv_denot (mo_E regs Bw) (SData 0%nat k 8) = Z_to_bv 64 (TW.u_at Bw k 8%nat).
Proof.
  intros regs Bw k. cbn [sv_denot]. f_equal.
  all: unfold data_word, TW.u_at, TW.sub; rewrite mo_ed; reflexivity.
Qed.

Lemma mo_data_s : forall regs Bw k,
  sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat k 4)) = Z_to_bv 64 (TW.s32_at Bw k).
Proof.
  intros regs Bw k.
  change (sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat k 4)))
    with (sext 64 (bv_extract 0 32 (sv_denot (mo_E regs Bw) (SData 0%nat k 4)))).
  rewrite (mo_data_u4 regs Bw k).
  pose proof (TWL.u_at_range Bw k 4%nat) as HR. change (8 * Z.of_nat 4) with 32 in HR.
  unfold TW.s32_at. rewrite <- (tw_sext_u Bw k 4%nat 32) by reflexivity. f_equal.
  apply bv_eq. rewrite !bv_extract_unsigned, !Z.shiftr_0_r, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (TW.u_at Bw k 4%nat) (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma mo_d_state : forall regs Bw,
  sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat 12 4)) = Z_to_bv 64 (TW.M_state Bw).
Proof. intros. rewrite mo_data_s. reflexivity. Qed.
Lemma mo_d_e2 : forall regs Bw,
  sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat 16 4)) = Z_to_bv 64 (TW.M_e2_acked Bw).
Proof. intros. rewrite mo_data_s. reflexivity. Qed.
Lemma mo_d_e1 : forall regs Bw,
  sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat 20 4)) = Z_to_bv 64 (TW.M_e1_us Bw).
Proof. intros. rewrite mo_data_s. reflexivity. Qed.
Lemma mo_d_n : forall regs Bw,
  sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat 65312 4)) = Z_to_bv 64 (TW.OW_n Bw).
Proof. intros. rewrite mo_data_s. reflexivity. Qed.

(* The 8-byte value the code stores at M.next_ka. *)
Lemma mo_d_ka : forall regs Bw,
  sv_denot (mo_E regs Bw)
    (SAlu ALU_ADD (SMd M_MUL (SData 0%nat 65048 4) (SLit 1000)) (SData 0%nat 32 8)) = Z_to_bv 64 (MO_KA Bw).
Proof.
  intros regs Bw.
  pose proof (TWL.u_at_range Bw 65048 4%nat) as HK. change (8 * Z.of_nat 4) with 32 in HK.
  pose proof (TWL.u_at_range Bw 32 8%nat) as HL. change (8 * Z.of_nat 8) with 64 in HL.
  rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
  rewrite (U_SLit _ 1000), (zcanon_id 1000) by (unfold M64; lia).
  unfold U. rewrite (mo_data_u4 regs Bw 65048), (mo_data_u8 regs Bw 32).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (TW.u_at Bw 65048 4%nat) (2 ^ 64)) by lia.
  rewrite (Z.mod_small (TW.u_at Bw 32 8%nat) (2 ^ 64)) by lia.
  unfold MO_KA, TCB.h_ms_m, TS0.u64, zcanon, M64.
  change (TW.M_last_rx Bw) with (TW.u_at Bw 32 8%nat).
  change (TW.Cfg_keepalive_ms Bw) with (TW.u_at Bw 65048 4%nat).
  f_equal. lia.
Qed.

(* ---- the regions at the entry ---- *)

Lemma mo_tw_in_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof.
  intros x (o & b & n & Hin & Hx).
  assert (HG : In (b, n) TG.G_HARNESS) by exact (TMAP_A_in_G o b n Hin).
  unfold inG. apply Exists_exists. exists (b, n). split; [exact HG | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma mo_inG_M : forall a, TA_M <= a < TA_M + TW.SZ_M -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply mo_tw_in_G. exists TW.OFF_M, TA_M, TW.SZ_M. split; [exact TMAP_A_M | lia]. Qed.

Lemma mo_inG_OW : forall a, TA_OW <= a < TA_OW + TW.SZ_OW -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply mo_tw_in_G. exists TW.OFF_OW, TA_OW, TW.SZ_OW. split; [exact TMAP_A_OW | lia]. Qed.

Lemma mo_gwr : forall a, inG TG.G_HARNESS a -> forall m, writable_at segs m a.
Proof. intros a Ha m. exact (gx_rw_writable segs TG.G_HARNESS a G_HARNESS_rw Ha m). Qed.

(* A CData chunk over the world data block holds the world's bytes at the matching image base. *)
Lemma mo_dchunk : forall (W : world segs) mem Bw (E : env) o b n (src len base co : Z),
  tw_at TMAP_A (aview segs (w_H W) mem) Bw -> In (o, b, n) TMAP_A -> ed E 0%nat = Bw ->
  o <= src -> 0 <= len -> src + len <= o + n -> base + co = b + (src - o) ->
  YP09.chunk_ok segs E (mrestrict (w_H W) mem) base (YP09.mkChunk co (CData 0%nat src len)).
Proof.
  intros W mem Bw E o b n src len base co Htw Hin Hed Ho Hlen Hsl Hbc i Hi.
  cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in Hi |- *.
  pose proof (tw_row TMAP_A o b n TMAP_A_ok Hin) as (Ho' & Hn & HoW & Hb & Hb64).
  destruct Htw as (HL & HR).
  assert (HLZ : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
  specialize (HR o b n (src - o + i) Hin ltac:(lia)).
  unfold aview in HR.
  destruct (YP09.mbyte segs (mrestrict (w_H W) mem) (b + (src - o + i))) as [bt|] eqn:Hmb; [|discriminate HR].
  cbn [option_map] in HR. injection HR as HR.
  replace (Z.to_nat (o + (src - o + i))) with (Z.to_nat (src + i)) in HR by (f_equal; lia).
  exists bt. split.
  - cbn [YP09.cbyte]. rewrite Hed.
    rewrite (nth_error_nth' Bw (Z_to_bv 8 0)) by lia.
    f_equal. apply bv_eq. symmetry. exact HR.
  - rewrite Hbc. replace (b + (src - o) + i) with (b + (src - o + i)) by lia. exact Hmb.
Qed.

(* A data region: its base atom's value, its bounds, the writability of its window, its one chunk. *)
Lemma mo_dreg : forall (W : world segs) mem (E : env) (nn : nat) (bb lo hi wlo whi : Z) (ch : YP09.chunk),
  bv_unsigned (ew E nn) = bb -> 0 <= bb + lo -> bb + hi <= 2 ^ 64 ->
  (forall a, bb + wlo <= a < bb + whi -> writable_at segs (mrestrict (w_H W) mem) a) ->
  YP09.chunk_ok segs E (mrestrict (w_H W) mem) bb ch ->
  region_ok segs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some nn) lo hi wlo whi [ch]).
Proof.
  intros W mem E nn bb lo hi wlo whi ch Hb Hlo Hhi Hw Hch. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hb. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
  constructor; [exact Hch | constructor].
Qed.

(* The two runtime-cell regions hold what transport_cells says they hold, at any AR state (E2's scfg_img_ok). *)
Lemma mo_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct mo_vals as (V1 & V93 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|]. split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
      [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V93; unfold FCells.CELL_K; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by (rewrite V93; unfold FCells.CELL_K; lia).
    split; [rewrite V93; unfold FCells.CELL_K; lia|]. split; [rewrite V93; unfold FCells.CELL_K; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
Qed.

(* OW's 304 payload bytes are addressable at every AR state: the shadow of its 38 granules is 0. *)
Lemma mo_ra : forall ly S (W : world segs) mem md,
  trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TA_OW TW.SZ_OW.
Proof.
  intros ly S W mem md HZ HAR x Hx.
  assert (EC : TA_OW = 6238304) by reflexivity.
  assert (ES : TW.SZ_OW = 304) by reflexivity.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
  rewrite EC, ES in Hx.
  assert (Hz := decode_zshadow_rd B ly S W mem md TA_OW (TA_OW + TW.SZ_OW) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(rewrite EC; lia) ltac:(rewrite EC, ES; lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow entry holds at every AR state. *)
Lemma mo_shok : forall ly S (W : world segs) mem md (E : env),
  trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 12) = Z_to_bv 64 TA_OW -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs MO_Bx MO_SH E (mrestrict (w_H W) mem).
Proof.
  intros ly S W mem md E HZ HAR E12 E32.
  unfold sh_ok, MO_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem E MO_Bx (A_OBJ 12) TA_OW TW.SZ_OW TA_OW 0 TW.SZ_OW
    (mo_ra ly S W mem md HZ HAR)).
  - unfold U, MO_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold TA_OW. lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, TA_OW, TW.SZ_OW in *. lia.
Qed.

(* The entry state and its shadow entry. *)
Lemma mo_entry : forall ly S (W : world segs) regs mem md Bw,
  transport_cells B -> trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  (forall a, spZ regs - MONLINE_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (mo_E regs Bw) ss_mo
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_maybe_online)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs MO_Bx MO_SH (mo_E regs Bw) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md Bw HCELLS HOW HAR Htw Hpres Hsp Hsp16.
  destruct mo_vals as (V1 & V93 & V8 & V12 & V30 & _).
  assert (EOB : forall j, (j < 95)%nat -> ew (mo_E regs Bw) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; rewrite mo_ew; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E32 : ew (mo_E regs Bw) 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite mo_ew; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew (mo_E regs Bw) 2) = spZ regs)
    by (rewrite mo_ew; rewrite (ew_Eimg_Ereg_nat regs _ 2%nat 2%bv eq_refl); reflexivity).
  assert (U1 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 1)) = FCells.GOT_CELL_K)
    by (rewrite (EOB 1%nat ltac:(lia)), V1; apply unsigned_lit_small; unfold FCells.GOT_CELL_K; lia).
  assert (U93 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 93)) = FCells.CELL_K)
    by (rewrite (EOB 93%nat ltac:(lia)), V93; apply unsigned_lit_small; unfold FCells.CELL_K; lia).
  assert (U8 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 8)) = TA_M)
    by (rewrite (EOB 8%nat ltac:(lia)), V8; apply unsigned_lit_small; unfold TA_M; lia).
  assert (U12 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 12)) = TA_OW)
    by (rewrite (EOB 12%nat ltac:(lia)), V12; apply unsigned_lit_small; unfold TA_OW; lia).
  assert (U30 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 30)) = TA_g_cfg + 24)
    by (rewrite (EOB 30%nat ltac:(lia)), V30; apply unsigned_lit_small; unfold TA_g_cfg; lia).
  assert (E12 : ew (mo_E regs Bw) (A_OBJ 12) = Z_to_bv 64 TA_OW)
    by (rewrite (EOB 12%nat ltac:(lia)), V12; reflexivity).
  destruct (mo_img_ok ly S W mem md (mo_E regs Bw) HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 93%nat ltac:(lia)) E32)
    as [RG RC].
  split; [|exact (mo_shok ly S W mem md (mo_E regs Bw) HOW HAR E12 E32)].
  rewrite restrict_mkst_fx. unfold ss_mo, mo_regions.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply mo_regs_ok.
  - vm_compute. reflexivity.
  - apply Forall_cons.
    { unfold stack_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. unfold MONLINE_FRAME in *.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. unfold MONLINE_FRAME. lia. }
    apply Forall_cons; [exact RG|]. apply Forall_cons; [exact RC|].
    apply Forall_cons.
    { apply (mo_dreg W mem _ (A_OBJ 8) TA_M 12 24 12 16); [exact U8 | unfold TA_M; lia | unfold TA_M; lia | |].
      - intros a Ha. apply mo_gwr. apply mo_inG_M. unfold TW.SZ_M. lia.
      - apply (mo_dchunk W mem Bw _ TW.OFF_M TA_M TW.SZ_M 12 12 TA_M 12 Htw TMAP_A_M (mo_ed regs Bw));
          unfold TW.OFF_M, TW.SZ_M; lia. }
    apply Forall_cons.
    { apply (mo_dreg W mem _ (A_OBJ 8) TA_M 32 40 0 0); [exact U8 | unfold TA_M; lia | unfold TA_M; lia | |].
      - intros a Ha. lia.
      - apply (mo_dchunk W mem Bw _ TW.OFF_M TA_M TW.SZ_M 32 8 TA_M 32 Htw TMAP_A_M (mo_ed regs Bw));
          unfold TW.OFF_M, TW.SZ_M; lia. }
    apply Forall_cons.
    { apply (mo_dreg W mem _ (A_OBJ 8) TA_M 48 56 48 56); [exact U8 | unfold TA_M; lia | unfold TA_M; lia | |].
      - intros a Ha. apply mo_gwr. apply mo_inG_M. unfold TW.SZ_M. lia.
      - apply (mo_dchunk W mem Bw _ TW.OFF_M TA_M TW.SZ_M 48 8 TA_M 48 Htw TMAP_A_M (mo_ed regs Bw));
          unfold TW.OFF_M, TW.SZ_M; lia. }
    apply Forall_cons.
    { apply (mo_dreg W mem _ (A_OBJ 30) (TA_g_cfg + 24) 0 4 0 0);
        [exact U30 | unfold TA_g_cfg; lia | unfold TA_g_cfg; lia | |].
      - intros a Ha. lia.
      - apply (mo_dchunk W mem Bw _ TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg TW.A_Cfg_keepalive_ms 4
                 (TA_g_cfg + 24) 0 Htw TMAP_A_g_cfg (mo_ed regs Bw)).
        all: unfold TW.A_Cfg_keepalive_ms, TW.OFF_g_cfg, TW.SZ_g_cfg; lia. }
    apply Forall_cons; [|apply Forall_nil].
    { apply (mo_dreg W mem _ (A_OBJ 12) TA_OW 0 4 0 4); [exact U12 | unfold TA_OW; lia | unfold TA_OW; lia | |].
      - intros a Ha. apply mo_gwr. apply mo_inG_OW. unfold TW.SZ_OW. lia.
      - apply (mo_dchunk W mem Bw _ TW.OFF_OW TA_OW TW.SZ_OW TW.A_OW_n 4 TA_OW 0 Htw TMAP_A_OW (mo_ed regs Bw));
          unfold TW.A_OW_n, TW.OFF_OW, TW.SZ_OW; lia. }
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, mo_rM1, mo_rM2, mo_rM3, mo_rK, mo_rO, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. rewrite Usp, U1, U93, U8, U12, U30.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold FCells.GOT_CELL_K, FCells.CELL_K, TA_M, TA_OW, TA_g_cfg, MONLINE_FRAME in *.
    repeat split; first [exact I | lia].
  - unfold mo_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U12, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end.
    all: try exact I.
    all: try (first [lia | unfold TA_M, TA_OW; lia | unfold TA_M; reflexivity | unfold TA_OW; reflexivity]).
Qed.

(* The region of OW.t[n] is disjoint from the walk's eight regions (all_disjoint looks at bases and bounds only). *)
Lemma mo_rT_disj : forall regs Bw n, 0 <= n <= 15 -> 2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  all_disjoint (mo_E regs Bw) (mo_rT n) mo_regions.
Proof.
  intros regs Bw n Hn Hsp.
  destruct mo_vals as (V1 & V93 & V8 & V12 & V30 & _).
  assert (EOB : forall j, (j < 95)%nat -> ew (mo_E regs Bw) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; rewrite mo_ew; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew (mo_E regs Bw) 2) = spZ regs)
    by (rewrite mo_ew; rewrite (ew_Eimg_Ereg_nat regs [w64 SHADOW_OFF] 2%nat (2%bv : bv 5) eq_refl); reflexivity).
  assert (U1 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 1)) = FCells.GOT_CELL_K)
    by (rewrite (EOB 1%nat ltac:(lia)), V1; apply unsigned_lit_small; unfold FCells.GOT_CELL_K; lia).
  assert (U93 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 93)) = FCells.CELL_K)
    by (rewrite (EOB 93%nat ltac:(lia)), V93; apply unsigned_lit_small; unfold FCells.CELL_K; lia).
  assert (U8 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 8)) = TA_M)
    by (rewrite (EOB 8%nat ltac:(lia)), V8; apply unsigned_lit_small; unfold TA_M; lia).
  assert (U12 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 12)) = TA_OW)
    by (rewrite (EOB 12%nat ltac:(lia)), V12; apply unsigned_lit_small; unfold TA_OW; lia).
  assert (U30 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 30)) = TA_g_cfg + 24)
    by (rewrite (EOB 30%nat ltac:(lia)), V30; apply unsigned_lit_small; unfold TA_g_cfg; lia).
  apply all_disjoint_of_extents.
  unfold mo_rT, mo_regions, stack_region, got_regionP, bcell_regionP, mo_rM1, mo_rM2, mo_rM3, mo_rK, mo_rO,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  cbn [base_val]. rewrite Usp, U1, U93, U8, U12, U30.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold FCells.GOT_CELL_K, FCells.CELL_K, TA_M, TA_OW, TA_g_cfg, MONLINE_FRAME in *.
  repeat split; first [exact I | lia].
Qed.

(* ---- the callee-saved registers at the return (regs_preserved_of_st_ok, over ew only) ---- *)

Lemma mo_pres : forall (regs : bvmap 5 word) Bw (E : env) ss ms (H : word -> bool),
  (forall n, (n < 32)%nat -> ew E n = ew (mo_E regs Bw) n) ->
  st_ok_pi segs VAL E ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  aregs_preserved regs (ms_regs ms).
Proof.
  intros regs Bw E ss ms H HA HS Hcs r Hr.
  assert (Hin : In (Z_to_bv 5 r : bv 5) CALLEE_SAVED).
  { unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
    assert (Hq : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hq as [->|Hq]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
    subst. repeat (first [left; apply bv_eq; reflexivity | right]). }
  pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
  rewrite (st_ok_pi_restrict_reg H E ss ms _ HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
  pose proof (bv_unsigned_in_range 5 (Z_to_bv 5 r : bv 5)) as Hu. change (bv_modulus 5) with 32 in Hu.
  rewrite HA by lia. rewrite mo_ew.
  rewrite (ew_Eimg_Ereg_nat regs [w64 SHADOW_OFF] (Z.to_nat (bv_unsigned (Z_to_bv 5 r : bv 5)))
            (Z_to_bv 5 r : bv 5) ltac:(lia)).
  apply Z_to_bv_bv_unsigned.
Qed.

(* ---- the world relation, one store at a time ---- *)

(* The reader that is the final memory on the ranges l and the entry memory elsewhere. *)
Definition mo_inl (l : list (Z * Z)) (x : Z) : bool :=
  existsb (fun r => ((fst r <=? x) && (x <? fst r + snd r))%bool) l.
Definition mo_rdm (W : world segs) (mF memc : word -> option byte) (l : list (Z * Z)) : Z -> option Z :=
  fun x => if mo_inl l x then aview segs (w_H W) mF x else aview segs (w_H W) memc x.

Lemma mo_rdm_nil : forall (W : world segs) mF memc Bw,
  tw_at TMAP_A (aview segs (w_H W) memc) Bw -> tw_at TMAP_A (mo_rdm W mF memc []) Bw.
Proof. intros W mF memc Bw H. exact H. Qed.

Lemma mo_wstep : forall (W : world segs) mF memc l Bw o b n k (m : nat) v,
  tw_at TMAP_A (mo_rdm W mF memc l) Bw -> In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> aview segs (w_H W) mF (b + k + Z.of_nat j) = Some (YO.le_byte v m j)) ->
  tw_at TMAP_A (mo_rdm W mF memc ((b + k, Z.of_nat m) :: l)) (TW.upd Bw (o + k) (TW.put m v)).
Proof.
  intros W mF memc l Bw o b n k m v Htw Hin Hk Hkm Hval.
  apply (tw_write TMAP_A (mo_rdm W mF memc l) _ Bw o b n k m v TMAP_A_ok Htw Hin Hk Hkm).
  - intros j Hj. unfold mo_rdm, mo_inl. cbn [existsb fst snd].
    replace ((b + k <=? b + k + Z.of_nat j) && (b + k + Z.of_nat j <? b + k + Z.of_nat m))%bool with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    cbn [orb]. apply Hval. exact Hj.
  - intros x Hx Hn'. unfold mo_rdm, mo_inl. cbn [existsb fst snd].
    destruct ((b + k <=? x) && (x <? b + k + Z.of_nat m))%bool eqn:Eb.
    + exfalso. apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      exact (Hn' (conj E1 E2)).
    + cbn [orb]. reflexivity.
Qed.

Lemma mo_wdone : forall (W : world segs) mF memc l Bw,
  tw_at TMAP_A (mo_rdm W mF memc l) Bw ->
  (forall x, tw_in TMAP_A x -> mo_inl l x = false -> aview segs (w_H W) mF x = aview segs (w_H W) memc x) ->
  tw_at TMAP_A (aview segs (w_H W) mF) Bw.
Proof.
  intros W mF memc l Bw Htw Hk. apply (tw_kept TMAP_A (mo_rdm W mF memc l) _ Bw Htw).
  intros x Hx. unfold mo_rdm. destruct (mo_inl l x) eqn:Ex; [reflexivity | exact (Hk x Hx Ex)].
Qed.

(* The bytes a literal chunk leaves in the final memory. *)
Lemma mo_cval : forall (W : world segs) mF (E : env) (base co : Z) (wd : N) (val : sv) (v : Z) (c : nat) (addr : Z) j,
  YP09.chunk_ok segs E (mrestrict (w_H W) mF) base (YP09.mkChunk co (CVal wd val)) ->
  Z.of_N wd = Z.of_nat c -> sv_denot E val = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_nat c) ->
  addr = base + co -> (j < c)%nat -> (c <= 8)%nat ->
  aview segs (w_H W) mF (addr + Z.of_nat j) = Some (YO.le_byte v c j).
Proof.
  intros W mF E base co wd val v c addr j Hch Hwd Hval Hv -> Hj Hc8.
  assert (Hv64 : 0 <= v < 2 ^ 64).
  { split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia. }
  destruct (Hch (Z.of_nat j) ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (bt & Hb & Hm).
  cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb. rewrite Hval in Hb.
  unfold YP09.byte_of_word in Hb. injection Hb as <-.
  unfold aview. cbn [YP09.c_off] in Hm. rewrite Hm. cbn [option_map]. f_equal.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia.
  unfold YO.le_byte. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat c))) by lia. reflexivity.
Qed.

(* The bytes an unchanged CData chunk leaves: the entry memory's (path A's three windows). *)
Lemma mo_dsame : forall (W : world segs) m memc Bw (E : env) o b n (src len base co : Z),
  tw_at TMAP_A (aview segs (w_H W) memc) Bw -> In (o, b, n) TMAP_A -> ed E 0%nat = Bw ->
  YP09.chunk_ok segs E (mrestrict (w_H W) m) base (YP09.mkChunk co (CData 0%nat src len)) ->
  o <= src -> 0 <= len -> src + len <= o + n -> base + co = b + (src - o) ->
  forall i, 0 <= i < len -> aview segs (w_H W) m (base + co + i) = aview segs (w_H W) memc (base + co + i).
Proof.
  intros W m memc Bw E o b n src len base co Htw Hin Hed Hch Ho Hlen Hsl Hbc i Hi.
  pose proof (tw_row TMAP_A o b n TMAP_A_ok Hin) as (Ho' & Hn & HoW & Hb & Hb64).
  pose proof Htw as (HL & HR).
  assert (HLZ : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
  specialize (HR o b n (src - o + i) Hin ltac:(lia)).
  replace (Z.to_nat (o + (src - o + i))) with (Z.to_nat (src + i)) in HR by (f_equal; lia).
  destruct (Hch i ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (bt & Hb1 & Hb2).
  cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1. rewrite Hed in Hb1.
  rewrite (nth_error_nth' Bw (Z_to_bv 8 0)) in Hb1 by lia. injection Hb1 as Hb1.
  cbn [YP09.c_off] in Hb2.
  assert (Hm1 : aview segs (w_H W) m (base + co + i) = Some (bv_unsigned bt))
    by (unfold aview; rewrite Hb2; reflexivity).
  assert (Hm2 : aview segs (w_H W) memc (base + co + i)
                = Some (bv_unsigned (nth (Z.to_nat (src + i)) Bw (Z_to_bv 8 0))))
    by (replace (base + co + i) with (b + (src - o + i)) by lia; exact HR).
  rewrite Hm1, Hm2. f_equal. rewrite Hb1. reflexivity.
Qed.

(* ---- the post ---- *)

Lemma mo_wr_inG : forall Bw a, monline_wr Bw a -> inG TG.G_HARNESS a.
Proof.
  intros Bw a (_ & _ & _ & [Hka | Hms]).
  - unfold twa_fld, TW.A_M_next_ka, TW.OFF_M in Hka. apply mo_inG_M. unfold TW.SZ_M. lia.
  - destruct Hms as [(Hn & Ht) | [Hn | Hst]].
    + unfold twa_fld, TW.A_OW_t_state, TW.OFF_OW, TW.OW_t_ESZ in Ht. unfold TCB.TRANS_MAX in Hn.
      apply mo_inG_OW. unfold TW.SZ_OW. lia.
    + unfold twa_fld, TW.A_OW_n, TW.OFF_OW in Hn. apply mo_inG_OW. unfold TW.SZ_OW. lia.
    + unfold twa_fld, TW.A_M_state, TW.OFF_M in Hst. apply mo_inG_M. unfold TW.SZ_M. lia.
Qed.

Lemma mo_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B TG.G_HARNESS ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MONLINE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MONLINE_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MONLINE_STK <= a < spZ regs) -> ~ monline_wr Bw a ->
     aview segs (w_H W) mF a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  tw_at TMAP_A (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, @transport_monline_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' regsF mF mdF
    LAWS MTL HGX HAR Hwin Hce Hsp47 Hra HJF KA GA HTW HP RF1 mat.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : MONLINE_STK = 16) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
  unfold transport_monline_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold MONLINE_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc mF
      (spZ regs - MONLINE_STK) (spZ regs) (monline_wr Bw)
      (fun a => (spZ regs - MONLINE_STK <= a < spZ regs) \/ monline_wr Bw a) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - intros a Ha Hn. apply KA; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso.
      pose proof (GLOW a (mo_wr_inG Bw a Hw)) as Hl. unfold kLowMemEnd in *. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + apply HnG. exact (mo_wr_inG Bw a Hw).
    - intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact HTW.
Qed.

(* ---- the branch conditions in the model's terms ---- *)

Lemma mo_bne : forall regs Bw kk z, 0 <= z < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat kk 4)))
    (sv_denot (mo_E regs Bw) (SLit z)) = negb (TW.s32_at Bw kk =? z).
Proof.
  intros regs Bw kk z Hz. rewrite branch_ne_U. f_equal.
  unfold U. rewrite mo_data_s. cbn [sv_denot]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small z (2 ^ 64)) by lia.
  apply mo_mod_eqb; [apply TWL.s32_range | lia].
Qed.

Lemma mo_beq : forall regs Bw kk z, 0 <= z < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat kk 4)))
    (sv_denot (mo_E regs Bw) (SLit z)) = (TW.s32_at Bw kk =? z).
Proof.
  intros regs Bw kk z Hz. rewrite branch_eq_U.
  unfold U. rewrite mo_data_s. cbn [sv_denot]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small z (2 ^ 64)) by lia.
  apply mo_mod_eqb; [apply TWL.s32_range | lia].
Qed.

Lemma mo_blt : forall regs Bw kk z, -2 ^ 31 <= z < 2 ^ 31 ->
  branch_taken BC_LT (sv_denot (mo_E regs Bw) (SLit z))
    (sv_denot (mo_E regs Bw) (SExt true 32 (SData 0%nat kk 4))) = (z <? TW.s32_at Bw kk).
Proof.
  intros regs Bw kk z Hz. cbn [branch_taken]. rewrite mo_data_s. cbn [sv_denot].
  apply mo_br_slt; [lia | apply TWL.s32_range].
Qed.

Lemma mo_inl_in : forall l x b n, In (b, n) l -> b <= x < b + n -> mo_inl l x = true.
Proof.
  intros l x b n Hin Hx. unfold mo_inl. apply existsb_exists. exists (b, n).
  split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro.
  split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

(* ---- the tactics of the walk ---- *)

(* The write right of a run started at the walk's regions: the frame below sp (inside the caller's stack window),
   the read-only image regions (no writable byte) and the written ranges of G (bytes of G). *)
Ltac mo_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_x_nil
  | apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      try (lazymatch goal with HU : bv_unsigned (ew _ 249) = TA_M |- _ => rewrite HU in Ha end);
      try (lazymatch goal with HU : bv_unsigned (ew _ 253) = TA_OW |- _ => rewrite HU in Ha end);
      try (lazymatch goal with HU : bv_unsigned (ew _ (A_OBJ 8)) = TA_M |- _ => rewrite HU in Ha end);
      try (lazymatch goal with HU : bv_unsigned (ew _ (A_OBJ 12)) = TA_OW |- _ => rewrite HU in Ha end);
      first [ apply mo_inG_M; unfold TW.SZ_M; lia | apply mo_inG_OW; unfold TW.SZ_OW; lia ] |]
  | apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      try (lazymatch goal with HU : bv_unsigned (ew _ 2) = spZ _ |- _ => rewrite HU in Ha end);
      left; split; [unfold awr_byte; left; unfold MONLINE_STK, MONLINE_FRAME in *; lia | lia] |] ].

Ltac mo_rwbases H :=
  try (lazymatch goal with HU : bv_unsigned (ew _ 2) = spZ _ |- _ => rewrite HU in H end);
  try (lazymatch goal with HU : bv_unsigned (ew _ 249) = TA_M |- _ => rewrite HU in H end);
  try (lazymatch goal with HU : bv_unsigned (ew _ 253) = TA_OW |- _ => rewrite HU in H end);
  try (lazymatch goal with HU : bv_unsigned (ew _ 271) = TA_g_cfg + 24 |- _ => rewrite HU in H end);
  try (lazymatch goal with HU : bv_unsigned (ew _ (A_OBJ 8)) = TA_M |- _ => rewrite HU in H end);
  try (lazymatch goal with HU : bv_unsigned (ew _ (A_OBJ 12)) = TA_OW |- _ => rewrite HU in H end).

(* Every window of the walk's regions lies in mo_win / mo_winT. *)
Ltac mo_cover :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in
  let xx := fresh "xx" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros bb wlo whi xx Hin Hx; cbv beta;
  mo_win_tac Hin Hx ltac:(mo_rwbases Hx;
    unfold mo_win, MONLINE_STK, MONLINE_FRAME, TW.SZ_M, TW.SZ_OW in *;
    first [ left; lia | right; left; lia | right; right; left; lia | right; right; right; lia ]).

Ltac mo_coverT :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in
  let xx := fresh "xx" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros bb wlo whi xx Hin Hx; cbv beta;
  mo_win_tac Hin Hx ltac:(mo_rwbases Hx;
    unfold mo_winT, mo_win, MONLINE_STK, MONLINE_FRAME, TW.SZ_M, TW.SZ_OW in *;
    first [ left; left; lia | left; right; left; lia | left; right; right; left; lia
          | left; right; right; right; lia | right; lia ]).

(* The split at a branch the run stopped on. *)
Ltac mo_branch HSx :=
  lazymatch type of HSx with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict (w_H ?Wx) ?msx) =>
      let K := eval vm_compute in (run_K A_LIM MO_Bx MO_SH ss) in
      let why := psym_why_tok transport_tpi transport_tw K MO_Bx YC4b.Bspan MO_SH
                   (start K MO_Bx YC4b.Bspan MO_SH ss) in
      lazymatch why with
      | SR_branch ?c ?a ?b =>
          eapply (paj_branch _ Ex ss msx _ _ c a b HSx); clear HSx;
          let Hc := fresh "Hc" in intros Hc HSx
      | ?w => fail 1 "mo_branch: the run did not stop at a branch"
      end
  | ?T => fail 1 "mo_branch: bad state"
  end.

(* What a run keeps: the bytes outside the walk's windows are the entry memory's. *)
Ltac mo_kept KAx GAx KN GN :=
  lazymatch goal with
  | |- SRr _ ?Wx (mkCfg ?msx _) (transport_monline_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memcx _ ?regsx _ _) =>
    lazymatch goal with
    | HFrx : frame_of _ _ (mrestrict _ ?mprev) _ |- _ =>
      lazymatch goal with
      | HGx : mem_grows _ _ |- _ =>
        assert (KN : forall a, 0 <= a < 2 ^ 64 -> ~ mo_win (spZ regsx) a ->
                  aview segs (w_H Wx) (ms_mem msx) a = aview segs (w_H Wx) memcx a)
          by (intros aa Haa Hnn; transitivity (aview segs (w_H Wx) mprev aa);
              [ apply (kept_of_frame _ _ _ _ _ (mo_win (spZ regsx)) HFrx);
                [ mo_cover | exact Haa | exact Hnn ]
              | apply KAx; [exact Haa | exact Hnn] ]);
        assert (GN : forall a, apresent (w_H Wx) memcx a -> apresent (w_H Wx) (ms_mem msx) a)
          by (intros aa Haa; exact (apresent_grows _ _ _ aa HGx (GAx aa Haa)));
        clear KAx GAx
      end end
  end.

Ltac mo_keptT n0 KAx GAx KN GN :=
  lazymatch goal with
  | |- SRr _ ?Wx (mkCfg ?msx _) (transport_monline_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memcx _ ?regsx _ _) =>
    lazymatch goal with
    | HFrx : frame_of _ _ (mrestrict _ ?mprev) _ |- _ =>
      lazymatch goal with
      | HGx : mem_grows _ _ |- _ =>
        assert (KN : forall a, 0 <= a < 2 ^ 64 -> ~ mo_winT (spZ regsx) n0 a ->
                  aview segs (w_H Wx) (ms_mem msx) a = aview segs (w_H Wx) memcx a)
          by (intros aa Haa Hnn; transitivity (aview segs (w_H Wx) mprev aa);
              [ apply (kept_of_frame _ _ _ _ _ (mo_winT (spZ regsx) n0) HFrx);
                [ mo_coverT | exact Haa | exact Hnn ]
              | apply KAx; [exact Haa | intros Hw; apply Hnn; left; exact Hw] ]);
        assert (GN : forall a, apresent (w_H Wx) memcx a -> apresent (w_H Wx) (ms_mem msx) a)
          by (intros aa Haa; exact (apresent_grows _ _ _ aa HGx (GAx aa Haa)));
        clear KAx GAx
      end end
  end.

(* One entry of the written list is false in mo_inl: refute the window it covers. *)
Ltac mo_nl H := destruct H as [H|H]; [apply Z.leb_nle in H | apply Z.ltb_nlt in H]; lia.
Ltac mo_nl3 H1 H2 H3 :=
  rewrite ?Z.leb_gt, ?Z.ltb_ge in H1, H2, H3; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H1, H2, H3; lia.

(* A payload byte of the world is below the allocation ceiling, so it is outside the call's stack window. *)
Ltac mo_low x Hx HGXx :=
  let H := fresh "Hlow" in
  pose proof (transport_segs_low x (proj1 (HGXx x (mo_tw_in_G x Hx)))) as H;
  unfold kLowMemEnd in H.

(* The return: the callee-saved registers, then the post. *)
Ltac mo_ret HSx :=
  lazymatch goal with
  | |- SRr _ ?Wx (mkCfg ?msx _) (transport_monline_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?regsx _ _) =>
    let RF1 := fresh "RF1" in let HPF := fresh "HPF" in
    mo_reg HSx (1%bv : bv 5) (YK11.getr regsx 1) RF1
      ltac:(cbn [sv_denot]; rewrite mo_ew, (ew_Eimg_Ereg_nat regsx [w64 SHADOW_OFF] 1%nat (1%bv : bv 5) eq_refl),
            Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
    assert (HPF : aregs_preserved regsx (ms_regs msx))
      by (apply (mo_pres regsx _ _ _ _ _ ltac:(intros n Hn; reflexivity) HSx ltac:(vm_compute; reflexivity)));
    eapply (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport) _ _ _ _ _ _ HSx eq_refl
              ltac:(vm_compute; reflexivity));
    let mat' := fresh "mat" in intros mat';
    eapply mo_close; try eassumption; try lia
  end.

(* The tail of path A: one run to the `ret`, the three unchanged windows of G, the post with Bw' = Bw.
   Hg refutes the written range monline_wr Bw (one of the three tests of :239 failed here). *)
Ltac mo_tailA Hg RUNx HSx HJx SHOKx KAx GAx Htwx HGXx :=
  paj_run_tok RUNx HSx HJx SHOKx YC4b.Bspan;
  [ mo_awr
  | let KA2 := fresh "KA" in let GA2 := fresh "GA" in
    mo_kept KAx GAx KA2 GA2;
    lazymatch goal with
    | |- SRr _ ?Wx (mkCfg ?msx _) (transport_monline_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memcx _ ?regsx ?Bwx _) =>
      let D1 := fresh "DS" in let D3 := fresh "DS" in let DO := fresh "DS" in
      let KF := fresh "KAF" in let HT := fresh "HTW" in let RG := fresh "RG" in
      assert (D1 : forall i, 0 <= i < 12 ->
        aview segs (w_H Wx) (ms_mem msx) (TA_M + 12 + i) = aview segs (w_H Wx) memcx (TA_M + 12 + i))
        by (pose proof (st_ok_pi_region_nth _ _ _ 3 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_dsame Wx (ms_mem msx) memcx Bwx _ TW.OFF_M TA_M TW.SZ_M 12 12 TA_M 12 Htwx TMAP_A_M
                     (mo_ed regsx Bwx) RG ltac:(unfold TW.OFF_M; lia) ltac:(lia)
                     ltac:(unfold TW.OFF_M, TW.SZ_M; lia) ltac:(unfold TW.OFF_M; lia)));
      assert (D3 : forall i, 0 <= i < 8 ->
        aview segs (w_H Wx) (ms_mem msx) (TA_M + 48 + i) = aview segs (w_H Wx) memcx (TA_M + 48 + i))
        by (pose proof (st_ok_pi_region_nth _ _ _ 5 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_dsame Wx (ms_mem msx) memcx Bwx _ TW.OFF_M TA_M TW.SZ_M 48 8 TA_M 48 Htwx TMAP_A_M
                     (mo_ed regsx Bwx) RG ltac:(unfold TW.OFF_M; lia) ltac:(lia)
                     ltac:(unfold TW.OFF_M, TW.SZ_M; lia) ltac:(unfold TW.OFF_M; lia)));
      assert (DO : forall i, 0 <= i < 4 ->
        aview segs (w_H Wx) (ms_mem msx) (TA_OW + 0 + i) = aview segs (w_H Wx) memcx (TA_OW + 0 + i))
        by (pose proof (st_ok_pi_region_nth _ _ _ 7 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_dsame Wx (ms_mem msx) memcx Bwx _ TW.OFF_OW TA_OW TW.SZ_OW TW.A_OW_n 4 TA_OW 0 Htwx
                     TMAP_A_OW (mo_ed regsx Bwx) RG ltac:(unfold TW.A_OW_n, TW.OFF_OW; lia) ltac:(lia)
                     ltac:(unfold TW.A_OW_n, TW.OFF_OW, TW.SZ_OW; lia)
                     ltac:(unfold TW.A_OW_n, TW.OFF_OW; lia)));
      assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsx - MONLINE_STK <= a < spZ regsx) ->
        ~ monline_wr Bwx a -> aview segs (w_H Wx) (ms_mem msx) a = aview segs (w_H Wx) memcx a)
        by (intros aa Haa H1 H2;
            destruct (Z_le_gt_dec (TA_M + 12) aa) as [P1|P1], (Z_lt_ge_dec aa (TA_M + 16)) as [P2|P2],
                     (Z_le_gt_dec (TA_M + 48) aa) as [P3|P3], (Z_lt_ge_dec aa (TA_M + 56)) as [P4|P4],
                     (Z_le_gt_dec TA_OW aa) as [P5|P5], (Z_lt_ge_dec aa (TA_OW + 4)) as [P6|P6];
            first [ (replace aa with (TA_M + 12 + (aa - (TA_M + 12))) by lia; apply D1; lia)
                  | (replace aa with (TA_M + 48 + (aa - (TA_M + 48))) by lia; apply D3; lia)
                  | (replace aa with (TA_OW + 0 + (aa - (TA_OW + 0))) by lia; apply DO; lia)
                  | (apply KA2; [exact Haa | unfold mo_win; intros [Hw | [Hw | [Hw | Hw]]];
                                 unfold MONLINE_STK, TA_M, TA_OW in *; lia]) ]);
      assert (HT : tw_at TMAP_A (aview segs (w_H Wx) (ms_mem msx)) Bwx)
        by (apply (mo_wdone Wx (ms_mem msx) memcx [] Bwx (mo_rdm_nil Wx (ms_mem msx) memcx Bwx Htwx));
            intros x Hx _; mo_low x Hx HGXx; apply KF; [lia | lia | Hg]);
      mo_ret HSx
    end ].

(* The tail of path B: one run to the `ret`, the three stores, the post. *)
Ltac mo_tailB RUNx HSx HJx SHOKx KAx GAx Htwx HGXx HSTx HE2x HE1x :=
  paj_run_tok RUNx HSx HJx SHOKx YC4b.Bspan;
  [ mo_awr
  | let KA2 := fresh "KA" in let GA2 := fresh "GA" in
    mo_kept KAx GAx KA2 GA2;
    lazymatch goal with
    | |- SRr _ ?Wx (mkCfg ?msx _) (transport_monline_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memcx _ ?regsx ?Bwx _) =>
      let BKA := fresh "BKA" in let BN := fresh "BN" in let BST := fresh "BST" in
      let KF := fresh "KAF" in let HT := fresh "HTW" in let RG := fresh "RG" in
      assert (BKA : forall j, (j < 8)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_M + 48 + Z.of_nat j) = Some (YO.le_byte (MO_KA Bwx) 8 j))
        by (intros j Hj;
            pose proof (st_ok_pi_region_nth _ _ _ 5 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_M 48 8 _ (MO_KA Bwx) 8%nat (TA_M + 48) j RG
                     eq_refl (mo_d_ka regsx Bwx)
                     ltac:(unfold MO_KA, TS0.u64; apply Z.mod_pos_bound; lia)
                     eq_refl Hj ltac:(lia)));
      assert (BN : forall j, (j < 4)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_OW + 0 + Z.of_nat j)
          = Some (YO.le_byte (TW.OW_n Bwx + 1) 4 j))
        by (intros j Hj;
            pose proof (st_ok_pi_region_nth _ _ _ 7 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_OW 0 4 _ (TW.OW_n Bwx + 1) 4%nat (TA_OW + 0) j RG
                     eq_refl
                     ltac:(rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw];
                           rewrite (U_SLit _ 1), (zcanon_id 1) by (unfold M64; lia);
                           unfold U; rewrite mo_data_s;
                           change (TW.s32_at Bwx 65312) with (TW.OW_n Bwx);
                           rewrite Z_to_bv_unsigned;
                           unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
                           rewrite (Z.mod_small (TW.OW_n Bwx) (2 ^ 64))
                             by (unfold TCB.TRANS_MAX, TCB.INT_MAX in *; lia);
                           apply zcanon_id; unfold M64 in *;
                           unfold TCB.TRANS_MAX, TCB.INT_MAX in *; lia)
                     ltac:(cbn [Z.of_nat]; unfold TCB.TRANS_MAX, TCB.INT_MAX in *; lia)
                     eq_refl Hj ltac:(lia)));
      assert (BST : forall j, (j < 4)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_M + 12 + Z.of_nat j) = Some (YO.le_byte TCB.S_ONLINE 4 j))
        by (intros j Hj;
            pose proof (st_ok_pi_region_nth _ _ _ 3 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_M 12 4 _ TCB.S_ONLINE 4%nat (TA_M + 12) j RG
                     eq_refl eq_refl ltac:(unfold TCB.S_ONLINE; cbn [Z.of_nat]; lia) eq_refl Hj ltac:(lia)));
      assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsx - MONLINE_STK <= a < spZ regsx) ->
        ~ monline_wr Bwx a -> aview segs (w_H Wx) (ms_mem msx) a = aview segs (w_H Wx) memcx a)
        by (intros aa Haa H1 H2; apply KA2; [exact Haa|]; unfold mo_win; intros [Hw | [Hw | [Hw | Hw]]];
            [ lia
            | apply H2; split; [exact HSTx | split; [apply negb_true_iff, Z.eqb_neq; exact HE2x
              | split; [apply negb_true_iff, Z.eqb_neq; exact HE1x
              | right; right; right; unfold twa_fld, TW.A_M_state, TW.OFF_M, TA_M in *; lia]]]
            | apply H2; split; [exact HSTx | split; [apply negb_true_iff, Z.eqb_neq; exact HE2x
              | split; [apply negb_true_iff, Z.eqb_neq; exact HE1x
              | left; unfold twa_fld, TW.A_M_next_ka, TW.OFF_M, TA_M in *; lia]]]
            | apply H2; split; [exact HSTx | split; [apply negb_true_iff, Z.eqb_neq; exact HE2x
              | split; [apply negb_true_iff, Z.eqb_neq; exact HE1x
              | right; right; left; unfold twa_fld, TW.A_OW_n, TW.OFF_OW, TA_OW in *; lia]]] ]);
      assert (HT : tw_at TMAP_A (aview segs (w_H Wx) (ms_mem msx))
        (TW.upd (TW.upd (TW.upd Bwx (TW.OFF_M + 48) (TW.put 8 (MO_KA Bwx)))
           (TW.OFF_OW + 0) (TW.put 4 (TW.OW_n Bwx + 1))) (TW.OFF_M + 12) (TW.put 4 TCB.S_ONLINE)))
        by (let T0 := fresh "T" in let T1 := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in
            pose proof (mo_rdm_nil Wx (ms_mem msx) memcx Bwx Htwx) as T0;
            pose proof (mo_wstep Wx (ms_mem msx) memcx [] Bwx TW.OFF_M TA_M TW.SZ_M 48 8%nat (MO_KA Bwx)
                          T0 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_nat]; lia) BKA) as T1;
            pose proof (mo_wstep Wx (ms_mem msx) memcx _ _ TW.OFF_OW TA_OW TW.SZ_OW 0 4%nat (TW.OW_n Bwx + 1)
                          T1 TMAP_A_OW ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat]; lia) BN) as T2;
            pose proof (mo_wstep Wx (ms_mem msx) memcx _ _ TW.OFF_M TA_M TW.SZ_M 12 4%nat TCB.S_ONLINE
                          T2 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_nat]; lia) BST) as T3;
            apply (mo_wdone Wx (ms_mem msx) memcx _ _ T3);
            intros x Hx Hnl; mo_low x Hx HGXx;
            unfold mo_inl in Hnl; cbn [existsb fst snd] in Hnl;
            rewrite !orb_false_iff in Hnl; destruct Hnl as (NL1 & NL2 & NL3 & _);
            rewrite !andb_false_iff in NL1, NL2, NL3;
            apply KA2; [lia|]; unfold mo_win; intros [Hw | [Hw | [Hw | Hw]]];
            [ lia | mo_nl NL1 | mo_nl NL3 | mo_nl NL2 ]);
      mo_ret HSx
    end ].

(* The tail of path C(n0): pin OW.n to n0, add the region of OW.t[n0], run to the `ret`, the six stores,
   the post. Enx : TW.OW_n Bw = n0. *)
Ltac mo_tailC n0 Enx RUNx HSx HJx SHOKx KAx GAx Htwx HGXx HSTx HE2x HE1x :=
  lazymatch goal with
  | |- SRr _ ?W0x (mkCfg _ _) (transport_monline_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?regs0 ?Bw0 _) =>
    let QN := fresh "QN" in
    mo_reg HSx (Z_to_bv 5 14) (Z_to_bv 64 n0) QN ltac:(rewrite mo_d_n, Enx; reflexivity);
    let HS2 := fresh "HSp" in
    pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 14) n0 HSx QN ltac:(vm_compute; reflexivity)) as HS2;
    clear HSx QN; rename HS2 into HSx;
    lazymatch type of HSx with
    | st_ok_pi _ _ ?Ey ?ssy (restrict (w_H ?Wy) ?msy) =>
      let ROK := fresh "ROK" in let RDJ := fresh "RDJ" in let HS3 := fresh "HSr" in
      assert (ROK : region_ok segs Ey (mrestrict (w_H Wy) (ms_mem msy)) (mo_rT n0))
        by (unfold mo_rT, region_ok;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
            lazymatch goal with HU : bv_unsigned (ew _ (A_OBJ 12)) = TA_OW |- _ => rewrite HU end;
            split; [unfold TA_OW; lia|]; split; [unfold TA_OW; lia|];
            split; [intros o Ho; apply mo_gwr; apply mo_inG_OW; unfold TW.SZ_OW; lia
                   | apply Forall_nil]);
      assert (RDJ : all_disjoint Ey (mo_rT n0) (ss_mem ssy))
        by (lazymatch goal with
            | Hsp' : 2 ^ 46 <= spZ _ <= 2 ^ 47 |- _ =>
              exact (all_disjoint_extents Ey (mo_rT n0) (mo_rT n0) mo_regions (ss_mem ssy) eq_refl
                       ltac:(vm_compute; reflexivity) (mo_rT_disj regs0 Bw0 n0 ltac:(lia) Hsp'))
            end);
      pose proof (st_ok_pi_add_region Ey ssy (restrict (w_H Wy) msy) (mo_rT n0) HSx
                    ltac:(vm_compute; reflexivity) ROK RDJ) as HS3;
      clear ROK RDJ; clear HSx; rename HS3 into HSx
    end
  end;
  paj_run_tok RUNx HSx HJx SHOKx YC4b.Bspan;
  [ mo_awr
  | let KA2 := fresh "KA" in let GA2 := fresh "GA" in
    mo_keptT n0 KAx GAx KA2 GA2;
    lazymatch goal with
    | |- SRr _ ?Wx (mkCfg ?msx _) (transport_monline_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memcx _ ?regsx ?Bwx _) =>
      let BKA := fresh "BKA" in let BT1 := fresh "BT" in let BT2 := fresh "BT" in let BT3 := fresh "BT" in
      let BN := fresh "BN" in let BST := fresh "BST" in let RG := fresh "RG" in let RT := fresh "RT" in
      let KF := fresh "KAF" in let HT := fresh "HTW" in
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HSx eq_refl) as RT; cbn [ms_mem restrict] in RT;
      destruct RT as (_ & _ & _ & RT); cbn [base_val] in RT; mo_rwbases RT;
      assert (BT3 : forall j, (j < 4)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_OW + (12 + 12 * n0) + Z.of_nat j)
          = Some (YO.le_byte TCB.R_ONLINE 4 j))
        by (intros j Hj;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_OW (12 + 12 * n0) 4 _ TCB.R_ONLINE 4%nat
                     (TA_OW + (12 + 12 * n0)) j (Forall_inv RT) eq_refl eq_refl
                     ltac:(unfold TCB.R_ONLINE; cbn [Z.of_nat]; lia) eq_refl Hj ltac:(lia)));
      assert (BT2 : forall j, (j < 4)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_OW + (8 + 12 * n0) + Z.of_nat j)
          = Some (YO.le_byte TCB.S_WAKING 4 j))
        by (intros j Hj;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_OW (8 + 12 * n0) 4 _ TCB.S_WAKING 4%nat
                     (TA_OW + (8 + 12 * n0)) j (Forall_inv (Forall_inv_tail RT)) eq_refl eq_refl
                     ltac:(unfold TCB.S_WAKING; cbn [Z.of_nat]; lia) eq_refl Hj ltac:(lia)));
      assert (BT1 : forall j, (j < 4)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_OW + (4 + 12 * n0) + Z.of_nat j)
          = Some (YO.le_byte TCB.S_ONLINE 4 j))
        by (intros j Hj;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_OW (4 + 12 * n0) 4 _ TCB.S_ONLINE 4%nat
                     (TA_OW + (4 + 12 * n0)) j (Forall_inv (Forall_inv_tail (Forall_inv_tail RT)))
                     eq_refl eq_refl ltac:(unfold TCB.S_ONLINE; cbn [Z.of_nat]; lia) eq_refl Hj ltac:(lia)));
      assert (BKA : forall j, (j < 8)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_M + 48 + Z.of_nat j) = Some (YO.le_byte (MO_KA Bwx) 8 j))
        by (intros j Hj;
            pose proof (st_ok_pi_region_nth _ _ _ 6 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_M 48 8 _ (MO_KA Bwx) 8%nat (TA_M + 48) j RG
                     eq_refl (mo_d_ka regsx Bwx)
                     ltac:(unfold MO_KA, TS0.u64; apply Z.mod_pos_bound; lia)
                     eq_refl Hj ltac:(lia)));
      assert (BN : forall j, (j < 4)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_OW + 0 + Z.of_nat j) = Some (YO.le_byte (n0 + 1) 4 j))
        by (intros j Hj;
            pose proof (st_ok_pi_region_nth _ _ _ 8 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_OW 0 4 _ (n0 + 1) 4%nat (TA_OW + 0) j RG
                     eq_refl eq_refl ltac:(cbn [Z.of_nat]; lia) eq_refl Hj ltac:(lia)));
      assert (BST : forall j, (j < 4)%nat ->
        aview segs (w_H Wx) (ms_mem msx) (TA_M + 12 + Z.of_nat j) = Some (YO.le_byte TCB.S_ONLINE 4 j))
        by (intros j Hj;
            pose proof (st_ok_pi_region_nth _ _ _ 4 _ HSx eq_refl) as RG; cbn [ms_mem restrict] in RG;
            destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG; cbn [base_val] in RG; mo_rwbases RG;
            exact (mo_cval Wx (ms_mem msx) (mo_E regsx Bwx) TA_M 12 4 _ TCB.S_ONLINE 4%nat (TA_M + 12) j RG
                     eq_refl eq_refl ltac:(unfold TCB.S_ONLINE; cbn [Z.of_nat]; lia) eq_refl Hj ltac:(lia)));
      assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsx - MONLINE_STK <= a < spZ regsx) ->
        ~ monline_wr Bwx a -> aview segs (w_H Wx) (ms_mem msx) a = aview segs (w_H Wx) memcx a)
        by (intros aa Haa H1 H2; apply KA2; [exact Haa|]; unfold mo_winT, mo_win;
            intros [[Hw | [Hw | [Hw | Hw]]] | Hw];
            [ lia
            | apply H2; split; [exact HSTx | split; [apply negb_true_iff, Z.eqb_neq; exact HE2x
              | split; [apply negb_true_iff, Z.eqb_neq; exact HE1x
              | right; right; right; unfold twa_fld, TW.A_M_state, TW.OFF_M, TA_M in *; lia]]]
            | apply H2; split; [exact HSTx | split; [apply negb_true_iff, Z.eqb_neq; exact HE2x
              | split; [apply negb_true_iff, Z.eqb_neq; exact HE1x
              | left; unfold twa_fld, TW.A_M_next_ka, TW.OFF_M, TA_M in *; lia]]]
            | apply H2; split; [exact HSTx | split; [apply negb_true_iff, Z.eqb_neq; exact HE2x
              | split; [apply negb_true_iff, Z.eqb_neq; exact HE1x
              | right; right; left; unfold twa_fld, TW.A_OW_n, TW.OFF_OW, TA_OW in *; lia]]]
            | apply H2; split; [exact HSTx | split; [apply negb_true_iff, Z.eqb_neq; exact HE2x
              | split; [apply negb_true_iff, Z.eqb_neq; exact HE1x
              | right; left; rewrite Enx; split;
                [unfold TCB.TRANS_MAX; lia
                | unfold twa_fld, TW.A_OW_t_state, TW.OFF_OW, TW.OW_t_ESZ, TA_OW in *; lia]]]] ]);
      assert (HT : tw_at TMAP_A (aview segs (w_H Wx) (ms_mem msx))
        (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd Bwx
           (TW.OFF_M + 48) (TW.put 8 (MO_KA Bwx)))
           (TW.OFF_OW + (4 + 12 * n0)) (TW.put 4 TCB.S_ONLINE))
           (TW.OFF_OW + (8 + 12 * n0)) (TW.put 4 TCB.S_WAKING))
           (TW.OFF_OW + (12 + 12 * n0)) (TW.put 4 TCB.R_ONLINE))
           (TW.OFF_OW + 0) (TW.put 4 (n0 + 1)))
           (TW.OFF_M + 12) (TW.put 4 TCB.S_ONLINE)))
        by (let T0 := fresh "T" in let T1 := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in
            let T4 := fresh "T" in let T5 := fresh "T" in let T6 := fresh "T" in
            pose proof (mo_rdm_nil Wx (ms_mem msx) memcx Bwx Htwx) as T0;
            pose proof (mo_wstep Wx (ms_mem msx) memcx [] Bwx TW.OFF_M TA_M TW.SZ_M 48 8%nat (MO_KA Bwx)
                          T0 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_nat]; lia) BKA) as T1; pose proof (mo_wstep Wx (ms_mem msx) memcx _ _ TW.OFF_OW TA_OW TW.SZ_OW (4 + 12 * n0) 4%nat
                          TCB.S_ONLINE T1 TMAP_A_OW ltac:(lia)
                          ltac:(unfold TW.SZ_OW; cbn [Z.of_nat]; lia) BT1) as T2; pose proof (mo_wstep Wx (ms_mem msx) memcx _ _ TW.OFF_OW TA_OW TW.SZ_OW (8 + 12 * n0) 4%nat
                          TCB.S_WAKING T2 TMAP_A_OW ltac:(lia)
                          ltac:(unfold TW.SZ_OW; cbn [Z.of_nat]; lia) BT2) as T3; pose proof (mo_wstep Wx (ms_mem msx) memcx _ _ TW.OFF_OW TA_OW TW.SZ_OW (12 + 12 * n0) 4%nat
                          TCB.R_ONLINE T3 TMAP_A_OW ltac:(lia)
                          ltac:(unfold TW.SZ_OW; cbn [Z.of_nat]; lia) BT3) as T4; pose proof (mo_wstep Wx (ms_mem msx) memcx _ _ TW.OFF_OW TA_OW TW.SZ_OW 0 4%nat (n0 + 1)
                          T4 TMAP_A_OW ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat]; lia) BN) as T5; pose proof (mo_wstep Wx (ms_mem msx) memcx _ _ TW.OFF_M TA_M TW.SZ_M 12 4%nat TCB.S_ONLINE
                          T5 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_nat]; lia) BST) as T6; apply (mo_wdone Wx (ms_mem msx) memcx _ _ T6);
            intros x Hx Hnl; mo_low x Hx HGXx;
            unfold mo_inl in Hnl; cbn [existsb fst snd] in Hnl;
            rewrite !orb_false_iff in Hnl;
            destruct Hnl as (NL1 & NL2 & NL3 & NL4 & NL5 & NL6 & _);
            rewrite !andb_false_iff in NL1, NL2, NL3, NL4, NL5, NL6;
            apply KA2; [lia|]; unfold mo_winT, mo_win;
            intros [[Hw | [Hw | [Hw | Hw]]] | Hw];
            first [ lia | mo_nl NL1 | mo_nl NL6 | mo_nl NL2 | mo_nl3 NL3 NL4 NL5 ]);
      mo_ret HSx
    end ].

Lemma mo_holds : @transport_m_maybe_online_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_maybe_online_cg_holds_stmt.
intros HCELLS HOW LAWS MTL HGX.
unfold transport_m_maybe_online_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw'
  HJ Hra Hra4 Hgp Htp Hsp16 Hlo Hhi Htw Hm Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MONLINE_STK = 16) by reflexivity.
assert (FF : MONLINE_FRAME = 16) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MONLINE_STK) by lia.
assert (Hwin : forall a, spZ regs - MONLINE_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
assert (HEI : img_env VAL A_LIM (mo_E regs Bw)) by apply mo_img_env.
destruct mo_vals as (V1 & V93 & V8 & V12 & V30 & VE).
assert (EOB : forall j, (j < 95)%nat -> ew (mo_E regs Bw) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
  by (intros j Hj; rewrite mo_ew; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew (mo_E regs Bw) 2) = spZ regs)
  by (rewrite mo_ew; rewrite (ew_Eimg_Ereg_nat regs [w64 SHADOW_OFF] 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (U1 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 1)) = FCells.GOT_CELL_K)
  by (rewrite (EOB 1%nat ltac:(lia)), V1; apply unsigned_lit_small; unfold FCells.GOT_CELL_K; lia).
assert (U93 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 93)) = FCells.CELL_K)
  by (rewrite (EOB 93%nat ltac:(lia)), V93; apply unsigned_lit_small; unfold FCells.CELL_K; lia).
assert (U8 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 8)) = TA_M)
  by (rewrite (EOB 8%nat ltac:(lia)), V8; apply unsigned_lit_small; unfold TA_M; lia).
assert (U12 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 12)) = TA_OW)
  by (rewrite (EOB 12%nat ltac:(lia)), V12; apply unsigned_lit_small; unfold TA_OW; lia).
assert (U30 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 30)) = TA_g_cfg + 24)
  by (rewrite (EOB 30%nat ltac:(lia)), V30; apply unsigned_lit_small; unfold TA_g_cfg; lia).
assert (N242 : bv_unsigned (ew (mo_E regs Bw) 242) = FCells.GOT_CELL_K) by exact U1.
assert (N334 : bv_unsigned (ew (mo_E regs Bw) 334) = FCells.CELL_K) by exact U93.
assert (N249 : bv_unsigned (ew (mo_E regs Bw) 249) = TA_M) by exact U8.
assert (N253 : bv_unsigned (ew (mo_E regs Bw) 253) = TA_OW) by exact U12.
assert (N271 : bv_unsigned (ew (mo_E regs Bw) 271) = TA_g_cfg + 24) by exact U30.
assert (RN : -2 ^ 31 <= TW.OW_n Bw < 2 ^ 31) by (unfold TW.OW_n; apply TWL.s32_range).
destruct (mo_entry lyc Sc W regs memc mdc Bw HCELLS HOW HAR Htw
  ltac:(intros a Ha; apply Hpres0; unfold MONLINE_FRAME in *; lia) Hsp Hsp16) as [HS SHOK].
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ mo_win (spZ regs) a ->
  aview segs (w_H W) memc a = aview segs (w_H W) memc a) by (intros; reflexivity).
assert (GA : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros a H; exact H).
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_maybe_online)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1: the frame, the save of ra, a2 = &M, M.state, `bne a1, a2` at +0x24 *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ mo_awr. }
mo_kept KA GA KA1 GA1.
mo_branch HS.
- (* path A1: M.state <> S_WAKING *)
  rewrite (mo_bne regs Bw 12 1 ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HB0 : Bw' = Bw) by exact (mo_model_keep Bw Bw' (or_introl Hc) Hm). subst Bw'.
  mo_tailA ltac:(intros Hgg; exact (Hc (proj1 Hgg))) RUN HS HJ SHOK KA1 GA1 Htw HGX.
- (* M.state = S_WAKING *)
  rewrite (mo_bne regs Bw 12 1 ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HST : TW.M_state Bw = TCB.S_WAKING) by exact Hc. clear Hc.
  (* run 2: M.e2_acked, `beqz` at +0x2c *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mo_awr. }
  mo_kept KA1 GA1 KA2 GA2.
  mo_branch HS.
  + (* path A2: M.e2_acked = 0 *)
    rewrite (mo_beq regs Bw 16 0 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (HE2z : TW.M_e2_acked Bw = 0) by exact Hc.
    assert (HB0 : Bw' = Bw) by exact (mo_model_keep Bw Bw' (or_intror (or_introl HE2z)) Hm). subst Bw'.
    mo_tailA ltac:(intros Hgg; destruct Hgg as (_ & Hgg & _); unfold TCB.truth in Hgg;
                   rewrite HE2z in Hgg; cbn in Hgg; discriminate Hgg) RUN HS HJ SHOK KA2 GA2 Htw HGX.
  + rewrite (mo_beq regs Bw 16 0 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
    assert (HE2 : TW.M_e2_acked Bw <> 0) by exact Hc. clear Hc.
    (* run 3: M.e1_us, `beqz` at +0x34 *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mo_awr. }
    mo_kept KA2 GA2 KA3 GA3.
    mo_branch HS.
    * (* path A3: M.e1_us = 0 *)
      rewrite (mo_beq regs Bw 20 0 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
      assert (HE1z : TW.M_e1_us Bw = 0) by exact Hc.
      assert (HB0 : Bw' = Bw) by exact (mo_model_keep Bw Bw' (or_intror (or_intror HE1z)) Hm). subst Bw'.
      mo_tailA ltac:(intros Hgg; destruct Hgg as (_ & _ & Hgg & _); unfold TCB.truth in Hgg;
                     rewrite HE1z in Hgg; cbn in Hgg; discriminate Hgg) RUN HS HJ SHOK KA3 GA3 Htw HGX.
    * rewrite (mo_beq regs Bw 20 0 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (HE1 : TW.M_e1_us Bw <> 0) by exact Hc. clear Hc.
      assert (HGU : TW.M_state Bw = TCB.S_WAKING /\ TCB.truth (TW.M_e2_acked Bw) = true /\
                    TCB.truth (TW.M_e1_us Bw) = true).
      { split; [exact HST|]. unfold TCB.truth. split; apply negb_true_iff, Z.eqb_neq; assumption. }
      (* run 4: M.last_rx, g_cfg.keepalive_ms, the shadow base, &OW, OW.n, the store at M + 48, `blt` at +0x64 *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { mo_awr. }
      mo_kept KA3 GA3 KA4 GA4.
      mo_branch HS.
      -- (* path B: 15 < OW.n *)
         rewrite (mo_blt regs Bw 65312 15 ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
         assert (HNn : 15 < TW.OW_n Bw) by exact Hc. clear Hc.
         destruct (mo_model_B Bw Bw' HLB HST HE2 HE1 ltac:(unfold TCB.TRANS_MAX; lia) Hm) as [HNI HB0].
         subst Bw'.
         mo_tailB RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1.
      -- (* path C: 0 <= OW.n <= 15 *)
         rewrite (mo_blt regs Bw 65312 15 ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
         assert (HNn : TW.OW_n Bw <= 15) by exact Hc. clear Hc.
         destruct (mo_model_C Bw Bw' HLB HST HE2 HE1 ltac:(unfold TCB.TRANS_MAX; lia) Hm) as [HN0 HB0].
         assert (HCASE : TW.OW_n Bw = 0 \/ TW.OW_n Bw = 1 \/ TW.OW_n Bw = 2 \/ TW.OW_n Bw = 3 \/
                         TW.OW_n Bw = 4 \/ TW.OW_n Bw = 5 \/ TW.OW_n Bw = 6 \/ TW.OW_n Bw = 7 \/
                         TW.OW_n Bw = 8 \/ TW.OW_n Bw = 9 \/ TW.OW_n Bw = 10 \/ TW.OW_n Bw = 11 \/
                         TW.OW_n Bw = 12 \/ TW.OW_n Bw = 13 \/ TW.OW_n Bw = 14 \/ TW.OW_n Bw = 15) by lia.
         subst Bw'.
         destruct HCASE as [En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|En]]]]]]]]]]]]]]];
           rewrite En;
           [ mo_tailC 0 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 1 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 2 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 3 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 4 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 5 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 6 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 7 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 8 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 9 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 10 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 11 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 12 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 13 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 14 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1
           | mo_tailC 15 En RUN HS HJ SHOK KA4 GA4 Htw HGX HST HE2 HE1 ].
Qed.

End mow.

Theorem transport_m_maybe_online_cg_holds :
  forall fx rc B MT, @transport_m_maybe_online_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@mo_holds fx rc B MT). Qed.
