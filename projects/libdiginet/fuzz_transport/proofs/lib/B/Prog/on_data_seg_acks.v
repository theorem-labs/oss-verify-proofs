(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 1050 of its 1124 lines of code are new or changed and 485 lines of the source are left out. *)
(* on_data_seg_acks: Theorem od_acks : forall fx rc B MT, @od_acks_stmt fx rc B MT (lib/B/Prog/on_data_seg_cut.v),
   the acks piece of the image-B walk of on_data, offsets +0x174 .. +0x23c of the listing
   lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x88bbc .. 0x88c84): from the return of send_control to
   the duplicate test (the cut od_dup_at, +0x240). Image B's twin of lib/A/Prog/on_data_seg_acks.v.

   What the code does (diginet_session.c:242-247). +0x174 `andi a1, s3, 7`: the UBSan alignment check of s;
   +0x178 `beqz a0`: a0 = r, send_control's result. r <> 0: +0x17c `beqz a1` to +0x1a8, else +0x180 `j` to the trap
   word `unimp` at +0x540. r = 0: +0x184 `bnez a1` to the trap word, else +0x188 - +0x1a4 the checked
   read-modify-write of stats.tx_acks (s + 18208 = s8 + 48). s = ONDATA_S = 0x5df640 is a multiple of 8, so a1 = 0 and
   neither path reaches the trap word: the token engine decides both tests of a1 from the fact on s3 (pinned to
   ONDATA_S, 64-aligned). Both paths, +0x1a8: the frame word F at s1 + 24; +0x1ac - +0x1cc the checked
   read-modify-write of stats.rx_data (s + 18160 = s8); s6 = fp + 28; a7 = its shadow address; +0x1d4 - +0x1d8 the
   2-byte check of fp + 28 (its shadow byte is 0: f's 64 bytes are marked usable, on_ack_cg.v trans_dframe_at's
   decode_rd_ok, carried to the cut's memory by od_cur's acall_kept_g); +0x1dc `lhu a2, 0(s6)` = fr_retry b
   (DgnTransportBCg.v frame_f_bytes' cell at 28); +0x1e0 `beqz a2`: 0 goes to +0x240. A retry: +0x1e4 - +0x200 the
   checked read-modify-write of stats.rx_desk_retries (s8 + 16), the 4-byte check of s + 36 and the 8-byte check of
   s + 192, +0x22c `lwu a0, 0(a0)` (S_cfg_backoff_ms), `mul` by 1000, `add` now (s7), +0x23c the store at s + 192
   (S_backoff_until_us). The world is then ondata_w2 B1 b r now (lib/B/Prog/on_data_cg.v).

   The runs are the token engine's over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x /
   paj_run_to_x); the two tests of r and of the retry are branches the engine cannot decide, taken apart by
   lib/B/Prog/DgnTransportBPaLib.v paj_branch. Four symbolic states: odac_ss1 at +0x174 (no region; s3 pinned to
   ONDATA_S), odac_ss1b at +0x188 (the 8 bytes of stats.tx_acks), odac_ss2a at +0x1a8 (the frame word at s1 + 24,
   stats.rx_data, the 2 bytes at f + 28) and odac_ss2b at +0x1e4 (stats.rx_desk_retries, S_cfg_backoff_ms and
   S_backoff_until_us); the shadow entries over s8, s3 and s4 decide the checks. Every store into g_s is a byte of G
   (W_journalG.v awr_ok_x_cons_g), the frame word a byte of the call's stack window; what the call has kept runs
   over them by on_data_seg_midkit.v odm_kept_step, and the world relation moves by TWorldG.v tw_write, once per
   store (odac_tws). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
on_data_cg on_data_seg_cut on_data_seg_midkit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require on_data.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module POD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.on_data.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The pcs where a run stops and a new symbolic state starts; the shadow span of a run with no check. *)
Definition ODAC_P188 : Z := AF_on_data + 0x188.
Definition ODAC_P1A8 : Z := AF_on_data + 0x1a8.
Definition ODAC_P1E4 : Z := AF_on_data + 0x1e4.
Definition ODAC_B0 : Z * Z := (0, 0).

(* The four fields the runs read and write, at their numeral offsets. *)
Lemma odac_txa : forall Bx, TW.S_stats_tx_acks Bx = TW.u_at Bx (TW.OFF_g_s + 18208) 8.
Proof.
intros Bx. unfold TW.S_stats_tx_acks, TW.A_S_stats_tx_acks.
replace (TW.OFF_g_s + 18152 + 56) with (TW.OFF_g_s + 18208) by reflexivity. reflexivity.
Qed.
Lemma odac_rxd : forall Bx, TW.S_stats_rx_data Bx = TW.u_at Bx (TW.OFF_g_s + 18160) 8.
Proof.
intros Bx. unfold TW.S_stats_rx_data, TW.A_S_stats_rx_data.
replace (TW.OFF_g_s + 18152 + 8) with (TW.OFF_g_s + 18160) by reflexivity. reflexivity.
Qed.
Lemma odac_drt : forall Bx, TW.S_stats_rx_desk_retries Bx = TW.u_at Bx (TW.OFF_g_s + 18176) 8.
Proof.
intros Bx. unfold TW.S_stats_rx_desk_retries, TW.A_S_stats_rx_desk_retries.
replace (TW.OFF_g_s + 18152 + 24) with (TW.OFF_g_s + 18176) by reflexivity. reflexivity.
Qed.
Lemma odac_cfg : forall Bx, TW.S_cfg_backoff_ms Bx = TW.u_at Bx (TW.OFF_g_s + 36) 4.
Proof.
intros Bx. unfold TW.S_cfg_backoff_ms, TW.A_S_cfg_backoff_ms.
replace (TW.OFF_g_s + 0 + 36) with (TW.OFF_g_s + 36) by reflexivity. reflexivity.
Qed.
Lemma odac_set_txa : forall Bx v, TW.set_S_stats_tx_acks Bx v = TW.upd Bx (TW.OFF_g_s + 18208) (TW.put 8 v).
Proof.
intros Bx v. unfold TW.set_S_stats_tx_acks, TW.A_S_stats_tx_acks.
replace (TW.OFF_g_s + 18152 + 56) with (TW.OFF_g_s + 18208) by reflexivity. reflexivity.
Qed.
Lemma odac_set_rxd : forall Bx v, TW.set_S_stats_rx_data Bx v = TW.upd Bx (TW.OFF_g_s + 18160) (TW.put 8 v).
Proof.
intros Bx v. unfold TW.set_S_stats_rx_data, TW.A_S_stats_rx_data.
replace (TW.OFF_g_s + 18152 + 8) with (TW.OFF_g_s + 18160) by reflexivity. reflexivity.
Qed.
Lemma odac_set_drt : forall Bx v,
  TW.set_S_stats_rx_desk_retries Bx v = TW.upd Bx (TW.OFF_g_s + 18176) (TW.put 8 v).
Proof.
intros Bx v. unfold TW.set_S_stats_rx_desk_retries, TW.A_S_stats_rx_desk_retries.
replace (TW.OFF_g_s + 18152 + 24) with (TW.OFF_g_s + 18176) by reflexivity. reflexivity.
Qed.
Lemma odac_set_bku : forall Bx v, TW.set_S_backoff_until_us Bx v = TW.upd Bx (TW.OFF_g_s + 192) (TW.put 8 v).
Proof. intros Bx v. unfold TW.set_S_backoff_until_us, TW.A_S_backoff_until_us. reflexivity. Qed.

(* ondata_w2 in two steps: the world after the test of r, then the rest. *)
Definition odac_wa (B1 : list byte) (r : Z) : list byte :=
  if r =? 0 then TW.set_S_stats_tx_acks B1 (TS0.u64 (TW.S_stats_tx_acks B1 + 1)) else B1.
Definition odac_wb (Ba b : list byte) (now : Z) : list byte :=
  let B := TW.set_S_stats_rx_data Ba (TS0.u64 (TW.S_stats_rx_data Ba + 1)) in
  if DSpec.fr_retry b =? 0 then B
  else
    let B := TW.set_S_stats_rx_desk_retries B (TS0.u64 (TW.S_stats_rx_desk_retries B + 1)) in
    TW.set_S_backoff_until_us B (TS0.u64 (now + TS0.ms_m (TW.S_cfg_backoff_ms B))).
Lemma odac_w2_eq : forall B1 b r now, ondata_w2 B1 b r now = odac_wb (odac_wa B1 r) b now.
Proof. intros B1 b r now. reflexivity. Qed.

Lemma odac_wa_0 : forall B1 r, r = 0 ->
  odac_wa B1 r = TW.upd B1 (TW.OFF_g_s + 18208) (TW.put 8 (TS0.u64 (TW.u_at B1 (TW.OFF_g_s + 18208) 8 + 1))).
Proof. intros B1 r ->. unfold odac_wa. rewrite Z.eqb_refl, odac_set_txa, odac_txa. reflexivity. Qed.
Lemma odac_wa_n0 : forall B1 r, r <> 0 -> odac_wa B1 r = B1.
Proof. intros B1 r Hr. unfold odac_wa. rewrite (proj2 (Z.eqb_neq r 0) Hr). reflexivity. Qed.

Lemma odac_wb_0 : forall Ba b now, DSpec.fr_retry b = 0 ->
  odac_wb Ba b now = TW.upd Ba (TW.OFF_g_s + 18160) (TW.put 8 (TS0.u64 (TW.u_at Ba (TW.OFF_g_s + 18160) 8 + 1))).
Proof. intros Ba b now H. unfold odac_wb. cbv zeta. rewrite H, Z.eqb_refl, odac_set_rxd, odac_rxd. reflexivity. Qed.

Lemma odac_wb_1 : forall Ba b now, length Ba = Z.to_nat TW.W_LEN -> DSpec.fr_retry b <> 0 ->
  0 <= TW.u_at Ba (TW.OFF_g_s + 36) 4 < 2 ^ 32 ->
  odac_wb Ba b now =
  TW.upd (TW.upd (TW.upd Ba (TW.OFF_g_s + 18160) (TW.put 8 (TS0.u64 (TW.u_at Ba (TW.OFF_g_s + 18160) 8 + 1))))
      (TW.OFF_g_s + 18176) (TW.put 8 (TS0.u64 (TW.u_at Ba (TW.OFF_g_s + 18176) 8 + 1))))
    (TW.OFF_g_s + 192) (TW.put 8 (TS0.u64 (now + TW.u_at Ba (TW.OFF_g_s + 36) 4 * 1000))).
Proof.
intros Ba b now HL Hr Hc. unfold odac_wb. cbv zeta. rewrite (proj2 (Z.eqb_neq _ 0) Hr).
rewrite odac_set_bku, odac_set_drt, odac_set_rxd, odac_cfg, odac_drt, odac_rxd.
set (v1 := TS0.u64 (TW.u_at Ba (TW.OFF_g_s + 18160) 8 + 1)).
assert (LBb : length (TW.upd Ba (TW.OFF_g_s + 18160) (TW.put 8 v1)) = Z.to_nat TW.W_LEN)
  by exact (proj2 (odm_gs_set Ba 18160 8 v1 HL ltac:(lia) ltac:(unfold TW.SZ_g_s; lia))).
rewrite (odm_gs_u_out Ba 18160 8 v1 (TW.OFF_g_s + 18176) 8 HL ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
  ltac:(unfold TW.OFF_g_s; lia) ltac:(right; lia)).
set (v2 := TS0.u64 (TW.u_at Ba (TW.OFF_g_s + 18176) 8 + 1)).
rewrite (odm_gs_u_out _ 18176 8 v2 (TW.OFF_g_s + 36) 4 LBb ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
  ltac:(unfold TW.OFF_g_s; lia) ltac:(left; lia)).
rewrite (odm_gs_u_out Ba 18160 8 v1 (TW.OFF_g_s + 36) 4 HL ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
  ltac:(unfold TW.OFF_g_s; lia) ltac:(left; lia)).
rewrite (odm_ms _ Hc). reflexivity.
Qed.

(* The world relation over one store into g_s, with the later stores' bytes still read at the old view. *)
Definition odac_inb (k : Z) (n : nat) (x : Z) : bool :=
  (ONDATA_S + k <=? x) && (x <? ONDATA_S + k + Z.of_nat n).
Lemma odac_inb_out : forall k n x, (x < ONDATA_S + k \/ ONDATA_S + k + Z.of_nat n <= x) -> odac_inb k n x = false.
Proof.
intros k n x H. unfold odac_inb. apply andb_false_iff.
destruct H; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.
Lemma odac_inb_false : forall k n x, odac_inb k n x = false -> ~ (ONDATA_S + k <= x < ONDATA_S + k + Z.of_nat n).
Proof.
intros k n x H Hx. unfold odac_inb in H.
rewrite (proj2 (Z.leb_le _ _) (proj1 Hx)), (proj2 (Z.ltb_lt _ _) (proj2 Hx)) in H. discriminate H.
Qed.

Lemma odac_tws : forall (rd rd' : Z -> option Z) (zb : Z -> bool) Bx k (n : nat) v,
  tw_at TMAP_B (fun x => if (zb x || odac_inb k n x)%bool then rd x else rd' x) Bx ->
  0 <= k -> k + Z.of_nat n <= TW.SZ_g_s ->
  (forall j, (j < n)%nat -> rd' (ONDATA_S + k + Z.of_nat j) = Some (YO0f.le_byte v n j)) ->
  (forall j, (j < n)%nat -> zb (ONDATA_S + k + Z.of_nat j) = false) ->
  tw_at TMAP_B (fun x => if zb x then rd x else rd' x) (TW.upd Bx (TW.OFF_g_s + k) (TW.put n v)).
Proof.
intros rd rd' zb Bx k n v Hat Hk Hn Hv Hz.
assert (CS : ONDATA_S = TB_g_s) by reflexivity.
apply (tw_write TMAP_B _ _ Bx TW.OFF_g_s TB_g_s TW.SZ_g_s k n v TMAP_B_ok Hat TMAP_B_g_s Hk Hn).
- intros j Hj. cbv beta. rewrite <- CS. rewrite (Hz j Hj). exact (Hv j Hj).
- intros x _ Hx. cbv beta. rewrite <- CS in Hx. rewrite (odac_inb_out k n x ltac:(lia)), orb_false_r.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Values the machine computes                                      *)
(* ------------------------------------------------------------------ *)

(* `srli`, `add s11`: the shadow address of an atom plus an offset. *)
Lemma odac_denot_shadow : forall E n m p c SHB,
  ew E n = Z_to_bv 64 p -> ew E m = Z_to_bv 64 SHB ->
  0 <= p < 2 ^ 64 -> 0 <= p + c < 2 ^ 64 -> 0 <= SHB -> SHB + (p + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SHB + (p + c) / 8).
Proof.
intros E n m p c SHB Hn Hm Hp Hpc HS1 HS2.
assert (HD : 0 <= (p + c) / 8) by (apply Z.div_pos; lia).
assert (Un : U E (SOff n c) = p + c) by exact (U_atom_off E n p c Hn Hp Hpc).
assert (Um : U E (SOff m 0) = SHB) by (rewrite (U_atom_off E m SHB 0 Hm) by lia; lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Un, Um, U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((p + c) / 8)) by (unfold M64; lia).
rewrite (Z.add_comm ((p + c) / 8) SHB). apply zcanon_id. unfold M64. lia.
Qed.

(* `lhu`: the zero extension of a 2-byte value. *)
Lemma odac_lhu : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
  sv_denot E (SExt false 16 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
rewrite U_SExt. rewrite (U_atom_off E n v 0 Hn) by lia. rewrite Z.add_0_r.
change (zcanon (v mod 2 ^ Z.of_N 16) = v). change (Z.of_N 16) with 16.
rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* `ld`, `addi 1`, `sd`: the 8 bytes the store leaves are those of the model's u64 of the sum. *)
Lemma odac_res1 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n 1)) mod 2 ^ (8 * Z.of_nat (N.to_nat 8)) =
  TS0.u64 (v + 1) mod 2 ^ (8 * Z.of_nat (N.to_nat 8)).
Proof.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn. rewrite (unsigned_lit_small v) by lia.
rewrite MState.unsigned_lit_wrap. unfold TS0.u64. change (8 * Z.of_nat (N.to_nat 8)) with 64.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* `lwu`, `mul` by 1000, `add` now: the backoff the store leaves, u64 (now + ms * 1000). *)
Lemma odac_bku_val : forall E n m cf now, ew E n = Z_to_bv 64 cf -> ew E m = Z_to_bv 64 now ->
  0 <= cf < 2 ^ 32 -> 0 <= now < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff n 0)) (SLit 1000)) (SOff m 0)))
    mod 2 ^ (8 * Z.of_nat (N.to_nat 8)) =
  TS0.u64 (now + cf * 1000) mod 2 ^ (8 * Z.of_nat (N.to_nat 8)).
Proof.
intros E n m cf now Hn Hm Hcf Hnow.
assert (HU : U E (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff n 0)) (SLit 1000)) (SOff m 0)) =
  (now + cf * 1000) mod 2 ^ 64).
{ rewrite U_SAlu, U_SMd, U_SExt, U_SLit.
  rewrite (U_atom_off E n cf 0 Hn) by lia. rewrite (U_atom_off E m now 0 Hm) by lia. rewrite !Z.add_0_r.
  cbn [zalu_raw zmd_raw]. change (Z.of_N 32) with 32.
  rewrite (Z.mod_small cf (2 ^ 32)) by lia.
  rewrite (zcanon_id cf) by (unfold M64; lia). rewrite (zcanon_id 1000) by (unfold M64; lia).
  rewrite (zcanon_id (cf * 1000)) by (unfold M64; lia).
  unfold zcanon, M64. f_equal. lia. }
unfold U in HU. rewrite HU. unfold TS0.u64. change (8 * Z.of_nat (N.to_nat 8)) with 64.
rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Section acks. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* ------------------------------------------------------------------ *)
(* 3. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* +0x174: no region; s3 pinned to ONDATA_S (64-aligned), so `andi a1, s3, 7` is 0 and the engine decides the two
   tests of a1 (+0x17c, +0x184); the run stops at `beqz a0` (+0x178). *)
Definition odac_ss1 : sstate :=
  mkSS OD_R1 sr_atoms [] None (mkFacts [(19%nat, mkAF ONDATA_S ONDATA_S 6)] [] []).
Definition odac_E1 (regs2 : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 0]).

Lemma odac_entry1 : forall (W2 : world segs) regs2 mem2,
  YK11.getr regs2 19 = w64 ONDATA_S ->
  st_ok_pi segs VAL (odac_E1 regs2) odac_ss1
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_R1)) mem2 (YK11.seg_rom segs))).
Proof.
intros W2 regs2 mem2 R19. rewrite restrict_mkst_fx. unfold odac_ss1.
assert (U19 : bv_unsigned (ew (odac_E1 regs2) 19) = ONDATA_S)
  by (unfold odac_E1; rewrite (can_ew_Eimg_Ereg_nat regs2 _ 19%nat (19%bv : bv 5) eq_refl), R19; unfold w64;
      apply unsigned_lit_small; unfold ONDATA_S, TB_g_s; lia).
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19.
  change (2 ^ 6) with 64.
  assert (M19 : ONDATA_S mod 64 = 0) by reflexivity.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [exact M19 | lia].
Qed.

(* +0x188 (r = 0): the 8 bytes of stats.tx_acks at s8 + 48, atom 33 their value; the shadow entry over s8. *)
Definition odac_rg_txa : YP09.region :=
  YP09.mkRegion (Some 24%nat) 48 56 48 56 [YP09.mkChunk 48 (CVal 8 (SOff 33 0))].
Definition odac_facts1b : facts :=
  mkFacts [(24%nat, mkAF (ONDATA_S + 18160) (ONDATA_S + 18160) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition odac_SH1b : list shent := [mkSHE 24 48 56].
Definition odac_Bx : sv := SOff 27 0.
Definition odac_ss1b : sstate := mkSS ODAC_P188 sr_atoms [odac_rg_txa] None odac_facts1b.
Definition odac_E1b (regs2 : bvmap 5 word) (tx : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 0; Z_to_bv 64 tx]).

Lemma odac_entry1b : forall (W2 : world segs) (regs2 : bvmap 5 word) mem2 (tx : Z),
  YK11.getr regs2 24 = w64 (ONDATA_S + 18160) -> YK11.getr regs2 27 = w64 SHADOW_OFF ->
  0 <= tx < 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 18208) 8 tx ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (ONDATA_S + 18208) 8 ->
  st_ok_pi segs VAL (odac_E1b regs2 tx) odac_ss1b
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ODAC_P188)) mem2 (YK11.seg_rom segs))) /\
  sh_ok segs odac_Bx odac_SH1b (odac_E1b regs2 tx) (mrestrict (w_H W2) mem2).
Proof.
intros W2 regs2 mem2 tx R24 R27 Htx HV HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := odac_E1b regs2 tx).
assert (U24 : bv_unsigned (ew E 24) = ONDATA_S + 18160)
  by (unfold E, odac_E1b; rewrite (can_ew_Eimg_Ereg_nat regs2 _ 24%nat (24%bv : bv 5) eq_refl), R24; unfold w64;
      apply unsigned_lit_small; unfold ONDATA_S, TB_g_s; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (unfold E, odac_E1b; rewrite (can_ew_Eimg_Ereg_nat regs2 _ 27%nat (27%bv : bv 5) eq_refl), R27; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = tx)
  by (unfold E, odac_E1b; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs2 _ 1);
      apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold odac_ss1b.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [odac_rg_txa YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [unfold ONDATA_S, TB_g_s; lia|]. split; [unfold ONDATA_S, TB_g_s; lia|].
    split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONDATA_S + 18160 + o) G_HARNESS_B_rw).
      apply odm_inG. unfold TW.SZ_g_s. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs E _ (ONDATA_S + 18160) 48 8 (SOff 33 0) tx);
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      replace (ONDATA_S + 18160 + 48) with (ONDATA_S + 18208) by lia. exact HV.
  + apply pairwise_disjoint_of_extents.
    unfold odac_rg_txa, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold odac_facts1b, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24, U27.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (M24 : (ONDATA_S + 18160) mod 16 = 0) by reflexivity.
    repeat match goal with |- _ /\ _ => split end; try exact I;
    unfold ONDATA_S, TB_g_s, SHADOW_OFF in *; first [exact M24 | lia].
- assert (UB : U E odac_Bx = SHADOW_OFF).
  { unfold U, odac_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, odac_SH1b. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W2) mem2 E odac_Bx 24 (ONDATA_S + 18208) 8 (ONDATA_S + 18160) 48 56 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small.
    unfold ONDATA_S, TB_g_s; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold ONDATA_S, TB_g_s, SHADOW_OFF in *. lia.
Qed.

(* The valuation of the two later states: the 32 registers, then two value atoms (33 and 34). *)
Definition odac_E3 (regs2 : bvmap 5 word) (v1 v2 : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 0; Z_to_bv 64 v1; Z_to_bv 64 v2]).
Lemma odac_ew3_reg : forall regs2 v1 v2 n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (odac_E3 regs2 v1 v2) n = YK11.getr regs2 rr.
Proof. intros regs2 v1 v2 n rr Hn. unfold odac_E3. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma odac_ew3_33 : forall regs2 v1 v2, ew (odac_E3 regs2 v1 v2) 33 = Z_to_bv 64 v1.
Proof. intros. unfold odac_E3. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 1). Qed.
Lemma odac_ew3_34 : forall regs2 v1 v2, ew (odac_E3 regs2 v1 v2) 34 = Z_to_bv 64 v2.
Proof. intros. unfold odac_E3. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 2). Qed.
Lemma odac_env3 : forall regs2 v1 v2, img_env VAL A_LIM (odac_E3 regs2 v1 v2).
Proof. intros. unfold odac_E3. apply Eimg_env. Qed.
Lemma odac_ew1b_reg : forall regs2 tx n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (odac_E1b regs2 tx) n = YK11.getr regs2 rr.
Proof. intros regs2 tx n rr Hn. unfold odac_E1b. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma odac_ew1b_33 : forall regs2 tx, ew (odac_E1b regs2 tx) 33 = Z_to_bv 64 tx.
Proof. intros. unfold odac_E1b. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 1). Qed.
Lemma odac_ew1_reg : forall regs2 n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (odac_E1 regs2) n = YK11.getr regs2 rr.
Proof. intros regs2 n rr Hn. unfold odac_E1. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma odac_env1 : forall regs2, img_env VAL A_LIM (odac_E1 regs2).
Proof. intros. unfold odac_E1. apply Eimg_env. Qed.
Lemma odac_env1b : forall regs2 tx, img_env VAL A_LIM (odac_E1b regs2 tx).
Proof. intros. unfold odac_E1b. apply Eimg_env. Qed.

(* +0x1a8: the frame word at s1 + 24 (written), stats.rx_data at s8 (atom 33), the 2 bytes at f + 28 (atom 34);
   the shadow entries over s8 and s4. The run stops at `beqz a2` (+0x1e0). *)
Definition odac_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition odac_rg_rxd : YP09.region :=
  YP09.mkRegion (Some 24%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition odac_rg_f28 : YP09.region :=
  YP09.mkRegion (Some 20%nat) 28 30 0 0 [YP09.mkChunk 28 (CVal 2 (SOff 34 0))].
Definition odac_facts2a : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF 4096 (2 ^ 47 - 192) 3);
           (24%nat, mkAF (ONDATA_S + 18160) (ONDATA_S + 18160) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition odac_SH2a : list shent := [mkSHE 24 0 8; mkSHE 20 0 64].
Definition odac_ss2a : sstate :=
  mkSS ODAC_P1A8 sr_atoms [odac_rg_slot; odac_rg_rxd; odac_rg_f28] None odac_facts2a.

Lemma odac_entry2a : forall (W2 : world segs) (regs2 : bvmap 5 word) mem2 (fp sp1 rx rt : Z),
  YK11.getr regs2 9 = w64 sp1 -> YK11.getr regs2 20 = w64 fp ->
  YK11.getr regs2 24 = w64 (ONDATA_S + 18160) -> YK11.getr regs2 27 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= fp -> fp mod 8 = 0 -> fp + 64 <= 2 ^ 47 - 128 ->
  (fp + 64 <= kLowShadowBeg \/ kHighMemBeg <= fp) ->
  (fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp) ->
  (fp + 64 <= sp1 + 24 \/ sp1 + 32 <= fp) ->
  0 <= rx < 2 ^ 64 -> 0 <= rt < 2 ^ 16 ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W2) mem2 a) ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 18160) 8 rx ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (fp + 28) 2 rt ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (ONDATA_S + 18160) 8 ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF fp 64 ->
  st_ok_pi segs VAL (odac_E3 regs2 rx rt) odac_ss2a
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ODAC_P1A8)) mem2 (YK11.seg_rom segs))) /\
  sh_ok segs odac_Bx odac_SH2a (odac_E3 regs2 rx rt) (mrestrict (w_H W2) mem2).
Proof.
intros W2 regs2 mem2 fp sp1 rx rt R9 R20 R24 R27 Hsp Hsp32 Hfp4 Hfp8 Hfph HAP HFG HOW
  Hrx Hrt Hpres HVrx HVrt HRA24 HRA20.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := odac_E3 regs2 rx rt).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E; apply odac_ew3_reg; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat (9%bv : bv 5) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = fp)
  by (rewrite (EE 20%nat (20%bv : bv 5) eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = ONDATA_S + 18160)
  by (rewrite (EE 24%nat (24%bv : bv 5) eq_refl), R24; unfold w64; apply unsigned_lit_small;
      unfold ONDATA_S, TB_g_s; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (EE 27%nat (27%bv : bv 5) eq_refl), R27; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = rx) by (unfold E; rewrite odac_ew3_33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = rt) by (unfold E; rewrite odac_ew3_34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold odac_ss2a.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [odac_rg_slot odac_rg_rxd odac_rg_f28
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    * rewrite U24. split; [unfold ONDATA_S, TB_g_s; lia|]. split; [unfold ONDATA_S, TB_g_s; lia|].
      split.
      -- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONDATA_S + 18160 + o) G_HARNESS_B_rw).
         apply odm_inG. unfold TW.SZ_g_s. lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val segs E _ (ONDATA_S + 18160) 0 8 (SOff 33 0) rx);
           [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
         rewrite Z.add_0_r. exact HVrx.
    * rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ fp 28 2 (SOff 34 0) rt);
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      exact HVrt.
  + apply pairwise_disjoint_of_extents.
    unfold odac_rg_slot, odac_rg_rxd, odac_rg_f28, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U20, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold ONDATA_S, TB_g_s, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, TW.SZ_g_s in *.
    repeat split;
      first [ exact I | lia
            | destruct HAP as [h | h]; lia
            | destruct HFG as [h | h]; lia
            | destruct HOW as [h | h]; lia ].
  + unfold odac_facts2a, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U20, U24, U27.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 4) with 16.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (M24 : (ONDATA_S + 18160) mod 16 = 0) by reflexivity.
    repeat match goal with |- _ /\ _ => split end; try exact I;
    unfold ONDATA_S, TB_g_s, SHADOW_OFF in *; first [exact M24 | exact Hsp32 | exact Hfp8 | lia].
- assert (UB : U E odac_Bx = SHADOW_OFF).
  { unfold U, odac_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, odac_SH2a. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range segs (w_H W2) mem2 E odac_Bx 24 (ONDATA_S + 18160) 8 (ONDATA_S + 18160) 0 8
      HRA24 UB).
    * unfold U. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small.
      unfold ONDATA_S, TB_g_s; lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold ONDATA_S, TB_g_s, SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range segs (w_H W2) mem2 E odac_Bx 20 fp 64 fp 0 64 HRA20 UB).
    * unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx.
      unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. destruct HAP as [h | h]; lia.
Qed.

(* +0x1e4 (a retry): stats.rx_desk_retries at s8 + 16 (atom 33), S_cfg_backoff_ms at s + 36 (atom 34),
   S_backoff_until_us at s + 192 (written); the shadow entries over s8 and s3. *)
Definition odac_rg_drt : YP09.region :=
  YP09.mkRegion (Some 24%nat) 16 24 16 24 [YP09.mkChunk 16 (CVal 8 (SOff 33 0))].
Definition odac_rg_cfg : YP09.region :=
  YP09.mkRegion (Some 19%nat) 36 40 0 0 [YP09.mkChunk 36 (CVal 4 (SOff 34 0))].
Definition odac_rg_bku : YP09.region := YP09.mkRegion (Some 19%nat) 192 200 192 200 [].
Definition odac_facts2b : facts :=
  mkFacts [(19%nat, mkAF ONDATA_S ONDATA_S 6); (24%nat, mkAF (ONDATA_S + 18160) (ONDATA_S + 18160) 4);
           (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition odac_SH2b : list shent := [mkSHE 24 16 24; mkSHE 19 36 200].
Definition odac_ss2b : sstate :=
  mkSS ODAC_P1E4 sr_atoms [odac_rg_drt; odac_rg_cfg; odac_rg_bku] None odac_facts2b.

Lemma odac_entry2b : forall (W2 : world segs) (regs2 : bvmap 5 word) mem2 (dr cf : Z),
  YK11.getr regs2 19 = w64 ONDATA_S ->
  YK11.getr regs2 24 = w64 (ONDATA_S + 18160) -> YK11.getr regs2 27 = w64 SHADOW_OFF ->
  0 <= dr < 2 ^ 64 -> 0 <= cf < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 18176) 8 dr ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 36) 4 cf ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (ONDATA_S + 18176) 8 ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (ONDATA_S + 36) 164 ->
  st_ok_pi segs VAL (odac_E3 regs2 dr cf) odac_ss2b
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ODAC_P1E4)) mem2 (YK11.seg_rom segs))) /\
  sh_ok segs odac_Bx odac_SH2b (odac_E3 regs2 dr cf) (mrestrict (w_H W2) mem2).
Proof.
intros W2 regs2 mem2 dr cf R19 R24 R27 Hdr Hcf HVdr HVcf HRA24 HRA19.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := odac_E3 regs2 dr cf).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E; apply odac_ew3_reg; exact Hn).
assert (U19 : bv_unsigned (ew E 19) = ONDATA_S)
  by (rewrite (EE 19%nat (19%bv : bv 5) eq_refl), R19; unfold w64; apply unsigned_lit_small;
      unfold ONDATA_S, TB_g_s; lia).
assert (U24 : bv_unsigned (ew E 24) = ONDATA_S + 18160)
  by (rewrite (EE 24%nat (24%bv : bv 5) eq_refl), R24; unfold w64; apply unsigned_lit_small;
      unfold ONDATA_S, TB_g_s; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (EE 27%nat (27%bv : bv 5) eq_refl), R27; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = dr) by (unfold E; rewrite odac_ew3_33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = cf) by (unfold E; rewrite odac_ew3_34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold odac_ss2b.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [odac_rg_drt odac_rg_cfg odac_rg_bku
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U24. split; [unfold ONDATA_S, TB_g_s; lia|]. split; [unfold ONDATA_S, TB_g_s; lia|].
      split.
      -- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONDATA_S + 18160 + o) G_HARNESS_B_rw).
         apply odm_inG. unfold TW.SZ_g_s. lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val segs E _ (ONDATA_S + 18160) 16 8 (SOff 33 0) dr);
           [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
         replace (ONDATA_S + 18160 + 16) with (ONDATA_S + 18176) by lia. exact HVdr.
    * rewrite U19. split; [unfold ONDATA_S, TB_g_s; lia|]. split; [unfold ONDATA_S, TB_g_s; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ ONDATA_S 36 4 (SOff 34 0) cf);
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      exact HVcf.
    * rewrite U19. split; [unfold ONDATA_S, TB_g_s; lia|]. split; [unfold ONDATA_S, TB_g_s; lia|].
      split; [|constructor]. intros o Ho.
      apply (gx_rw_writable segs TG.G_HARNESS_B (ONDATA_S + o) G_HARNESS_B_rw).
      apply odm_inG. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold odac_rg_drt, odac_rg_cfg, odac_rg_bku, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold ONDATA_S, TB_g_s in *. repeat split; first [exact I | lia].
  + unfold odac_facts2b, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U24, U27.
    change (2 ^ 6) with 64. change (2 ^ 4) with 16.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (M19 : ONDATA_S mod 64 = 0) by reflexivity.
    assert (M24 : (ONDATA_S + 18160) mod 16 = 0) by reflexivity.
    repeat match goal with |- _ /\ _ => split end; try exact I;
    unfold ONDATA_S, TB_g_s, SHADOW_OFF in *; first [exact M19 | exact M24 | lia].
- assert (UB : U E odac_Bx = SHADOW_OFF).
  { unfold U, odac_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, odac_SH2b. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range segs (w_H W2) mem2 E odac_Bx 24 (ONDATA_S + 18176) 8 (ONDATA_S + 18160) 16 24
      HRA24 UB).
    * unfold U. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small.
      unfold ONDATA_S, TB_g_s; lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold ONDATA_S, TB_g_s, SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range segs (w_H W2) mem2 E odac_Bx 19 (ONDATA_S + 36) 164 ONDATA_S 36 200 HRA19 UB).
    * unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small.
      unfold ONDATA_S, TB_g_s; lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold ONDATA_S, TB_g_s, SHADOW_OFF in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Tactics                                                           *)
(* ------------------------------------------------------------------ *)

Ltac odac_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
Ltac odac_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
(* the register r the run kept *)
Ltac odac_keep HS EEq n r R :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _);
      lazymatch goal with |- sv_denot ?E0 ?ee = ?v =>
        let e' := eval vm_compute in ee in change (sv_denot E0 e' = v) end;
      cbn [sv_denot]; rewrite (EEq n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R
  end.
Ltac odac_regs_s HS EEq R2 R3 R4 R8 R9 R25 R26 R18 R19 R20 R21 R27 :=
  unfold od_regs_s, od_regs_rel; repeat apply conj;
  [ odac_keep HS EEq 2%nat (2%bv : bv 5) R2 | odac_keep HS EEq 3%nat (3%bv : bv 5) R3
  | odac_keep HS EEq 4%nat (4%bv : bv 5) R4 | odac_keep HS EEq 8%nat (8%bv : bv 5) R8
  | odac_keep HS EEq 9%nat (9%bv : bv 5) R9 | odac_keep HS EEq 25%nat (25%bv : bv 5) R25
  | odac_keep HS EEq 26%nat (26%bv : bv 5) R26 | odac_keep HS EEq 18%nat (18%bv : bv 5) R18
  | odac_keep HS EEq 19%nat (19%bv : bv 5) R19 | odac_keep HS EEq 20%nat (20%bv : bv 5) R20
  | odac_keep HS EEq 21%nat (21%bv : bv 5) R21 | odac_keep HS EEq 27%nat (27%bv : bv 5) R27 ].
(* the register r of the machine state of HS, its symbolic value computed, then tac *)
Ltac odac_regv HS r tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _);
      lazymatch goal with |- sv_denot ?E0 ?ee = ?v =>
        let e' := eval vm_compute in ee in change (sv_denot E0 e' = v) end; tac
  end.
(* the write windows of a run lie in the set the goal names *)
Ltac odac_win :=
  let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b0 wlo whi x Hin Hx; cbv beta;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hx;
      repeat match goal with U : bv_unsigned (ew _ _) = _ |- _ => rewrite U in Hx end;
      first [lia | left; lia | right; lia] |]);
  destruct Hin.
(* the awr obligation of one region: the frame word (a byte of the call's window), a field of g_s, or no window *)
Ltac odac_awr_slot U9 :=
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
Ltac odac_awr_g U :=
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U in Ha;
    apply odm_inG; unfold TW.SZ_g_s; lia |].
Ltac odac_awr_0 :=
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].

(* ------------------------------------------------------------------ *)
(* 5. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma odac_acks : @od_acks_stmt fx rc B MT.
Proof.
unfold od_acks_stmt, od_r1_at.
intros DUP LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F B1 r f ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HPCS & HCELLS & HSC & HROU & HRNE & HROR & HRNO & LAWS & MTL & MTF & SMP & ASF & FFL & HGX
  & HGNE).
pose proof HFIX as (HPRE & HTFN & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HPRE as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hfn0
  & Hm & HTF & HROM & HAPT & HINV1 & HINV4 & HINV3 & Hcnt & Hev).
pose proof HCUR as (HCUR0 & Hsc & HTW1 & Hgf1).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as ((HRR & R18 & R19 & R20 & R21 & R27) & R22 & R23 & R24 & R10).
pose proof HRR as (R2 & R3 & R4 & R8 & R9 & R25 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDF as (Hcode & Hbuf0 & Hgb & Hsrc & Hdow & HnoG & Hfp0 & Hfp8 & Hfjl & Hgf & Hfake & Hrdok & Hfow).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0a & Hstk1 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4272 <= ONDATA_STK).
{ unfold ONDATA_STK, ONDATA_FRAME, ONDATA_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?bb =>
    pose proof (Z.le_max_l a bb) as Hm2; assert (Ha4 : a = 4096) by reflexivity end.
  lia. }
assert (Hsp1 : spZ regs - 192 < sp1 <= spZ regs - 160).
{ rewrite Esp1. unfold ONDATA_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M. lia. }
assert (Hsp1al : sp1 mod 32 = 0).
{ rewrite Esp1.
  replace (32 * ((spZ regs - ONDATA_FRAME) / 32)) with (((spZ regs - ONDATA_FRAME) / 32) * 32) by lia.
  apply Z_mod_mult. }
assert (Hsp1R : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (Hwin : alloc_ceiling <= spZ regs - ONDATA_STK) by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* f at the cut's memory *)
destruct (odm_f_kept B LAWS lyc Sc W memc mdc W2 mem2 (spZ regs - ONDATA_STK) (spZ regs) Bw b fp
  HARc HGX HK Hfake) as [KF KS].
assert (LB : length (frame_f_bytes buf b fj) = 64%nat).
{ unfold frame_f_bytes, frame_f_cells. rewrite Hcode. cbn [Z.eqb]. rewrite length_map.
  apply LC.cells_bytes_length. cbn [PParse.parse_cells LC.cells_wf LC.cell_wf].
  pose proof (odm_blen b Hcode) as Hb30.
  repeat split;
    first [ unfold DSpec.fr_dst; rewrite length_firstn; lia
          | unfold DSpec.fr_src; rewrite length_firstn, length_skipn; lia
          | rewrite length_firstn, length_skipn, Hfjl; lia
          | rewrite length_skipn, Hfjl; lia
          | exact I ]. }
assert (Hgb2 : YI00.garr8 segs (mrestrict (w_H W2) mem2) fp (frame_f_bytes buf b fj)).
{ intros j Hj. destruct (Hgf j Hj) as [HV HRg]. split; [|exact HRg].
  intros t Ht. rewrite <- (HV t Ht). apply odm_mb_eq. apply KF. rewrite LB in Hj. lia. }
pose proof (odm_f28 (mrestrict (w_H W2) mem2) fp buf b fj Hcode Hfjl Hgb2) as HV28.
pose proof Hrdok as (Hvis & HRAf & Hhull & Hamem & Hfp0' & Hfp63).
assert (HRAf2 : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF fp FRAME_F_SIZE).
{ intros x Hx. destruct (HRAf x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite KS by (unfold FRAME_F_SIZE in Hx; lia). exact Hs. }
unfold FRAME_F_SIZE in HRAf2.
(* f is apart from g_s, from the shadow band and from the stack window *)
destruct Hfake as (cid0 & pos0 & Hin0 & Hlo0 & Hhi0).
assert (HFNG : forall a, fp <= a < fp + 64 -> ~ (ONDATA_S <= a < ONDATA_S + TW.SZ_g_s)).
{ intros a Ha Hg0. destruct (HGX a (odm_inG a Hg0)) as [Hi _].
  exact (frm_img segs B LAWS lyc Sc W memc mdc cid0 pos0 a HARc Hin0
    ltac:(unfold FRAME_F_SIZE in Hhi0; lia) Hi). }
assert (HFG : fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp).
{ destruct (Z_le_gt_dec (fp + 64) ONDATA_S) as [h | h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONDATA_S + TW.SZ_g_s) fp) as [h2 | h2]; [right; exact h2|].
  exfalso. apply (HFNG (Z.max fp ONDATA_S)); unfold ONDATA_S, TB_g_s, TW.SZ_g_s in *; lia. }
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid0 pos0 HARc Hin0) as (_ & HFapp0 & _ & _).
pose proof (@ASAN_CEIL_range rc) as (HCE & _).
unfold in_app in HFapp0. unfold FRAME_F_SIZE in Hhi0.
assert (HAPf : fp + 64 <= kLowShadowBeg \/ kHighMemBeg <= fp).
{ destruct HFapp0 as (_ & [HL | (HH & _)]); [left | right]; lia. }
assert (Hfph : fp + 64 <= 2 ^ 47 - 128).
{ destruct HFapp0 as (_ & [HL | (HH & HC)]); unfold kLowShadowBeg in *; lia. }
assert (Hfp4 : 4096 <= fp) by (destruct HFapp0 as (H4 & _); lia).
assert (HOW : fp + 64 <= sp1 + 24 \/ sp1 + 32 <= fp).
{ unfold decode_off_win, FRAME_F_SIZE in Hfow. destruct Hfow as [h | h]; [left | right]; lia. }
(* the own frame is apart from g_s *)
assert (EFA : frame_addr ly2 ONDATA_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (HinF : In (ONDATA_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFfNG : forall a, F <= a < F + 256 -> ~ (ONDATA_S <= a < ONDATA_S + TW.SZ_g_s)).
{ intros a Ha Hg0. destruct (HGX a (odm_inG a Hg0)) as [Hi _].
  exact (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos a HAR2 HinF
    ltac:(rewrite EFA; change (fs_frame_bytes ONDATA_CID) with 256; lia) Hi). }
destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos HAR2 HinF) as (HF4096 & HFceil & _).
rewrite EFA in HF4096, HFceil. change (fs_frame_bytes ONDATA_CID) with 256 in HFceil.
(* the model's facts *)
assert (Hrr : - 2 ^ 63 <= r < 2 ^ 63) by exact (POD.od_send_control_r _ _ _ _ _ _ _ _ Hsc).
assert (LB1 : length B1 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ HTW1).
assert (Hrtr : 0 <= DSpec.fr_retry b < 2 ^ 16) by apply DSpec.be16_range.
(* ---- the cut od_dup_at, from any memory that changed only the five written ranges ---- *)
set (Zs := fun a => (ONDATA_S + 18208 <= a < ONDATA_S + 18216) \/ (sp1 + 24 <= a < sp1 + 32) \/
  (ONDATA_S + 18160 <= a < ONDATA_S + 18168) \/ (ONDATA_S + 18176 <= a < ONDATA_S + 18184) \/
  (ONDATA_S + 192 <= a < ONDATA_S + 200)).
assert (TODUP : forall (memE : word -> option byte) (mdE : Model) (regsE : bvmap 5 word),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONDATA_CID, pos) :: own) ly2 S2 W2 memE mdE (k + e) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) memE a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memE a) ->
  rdword (aview segs (w_H W2) memE) (sp1 + 24) = Some F ->
  tw_at TMAP_B (aview segs (w_H W2) memE) (ondata_w2 B1 b r now) ->
  od_regs_dup regs regsE fp b sp1 F ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsE (Z_to_bv 64 (BASE + OD_DUP)) memE (YK11.seg_rom segs)) mdE)
    (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b)).
{ intros memE mdE regsE HJE KP GA Hs24 TWE HRG.
  apply (DUP LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F B1 r f ly2 S2 W2 memE mdE e regsE HFIX); [|exact HRG].
  unfold od_dup_cur.
  refine (conj _ (conj Hs24 (conj Hsc (conj TWE Hgf1)))).
  unfold od_cur.
  refine (conj HJE (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj _ (conj _ _)))))))).
  - assert (HZS : forall a, Zs a -> (spZ regs - ONDATA_STK <= a < spZ regs) \/ ondata_wr Bw b a).
    { intros a [Ha | [Ha | [Ha | [Ha | Ha]]]].
      - right. unfold ondata_wr. right; right; left.
        unfold twb_fld, TW.A_S_stats_tx_acks, TW.OFF_g_s, ONDATA_S, TB_g_s in *. lia.
      - left. lia.
      - right. unfold ondata_wr. right; right; right; left.
        unfold twb_fld, TW.A_S_stats_rx_data, TW.OFF_g_s, ONDATA_S, TB_g_s in *. lia.
      - right. unfold ondata_wr. right; right; right; right; left.
        unfold twb_fld, TW.A_S_stats_rx_desk_retries, TW.OFF_g_s, ONDATA_S, TB_g_s in *. lia.
      - right. unfold ondata_wr. right; right; right; right; right; left.
        unfold twb_fld, TW.A_S_backoff_until_us, TW.OFF_g_s, ONDATA_S, TB_g_s in *. lia. }
    exact (odm_kept_step B LAWS lyc Sc W memc mdc W2 mem2 memE (spZ regs - ONDATA_STK) (spZ regs) Bw b Zs
      HARc HGX ltac:(lia) ltac:(lia) HZS HK KP GA).
  - apply Forall_forall. intros o Hin.
    assert (Hb : 8 <= fst o <= 104).
    { unfold OD_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
    apply (YF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) memE) (spZ regs - fst o)
      (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))).
    + intros i Hi. apply KP; [lia|]. unfold Zs, ONDATA_S, TB_g_s. lia.
    + exact (proj1 (Forall_forall _ _) Hsaved o Hin).
  - apply (YF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) memE) (F + OD_FBYTES - 8)
      (flag_addr lyc ONDATA_CID pos)); [|exact HFLw].
    intros i Hi. apply KP; [unfold OD_FBYTES in *; lia|].
    unfold Zs. intros [Hc | [Hc | [Hc | [Hc | Hc]]]];
      first [ exact (HFfNG (F + OD_FBYTES - 8 + i) ltac:(unfold OD_FBYTES; lia) ltac:(unfold TW.SZ_g_s; lia))
            | unfold OD_FBYTES in *; lia ]. }
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* ---- +0x1a8 .. +0x23c, from either path of the test of r ---- *)
assert (J1A8 : forall (m1 : word -> option byte) (md1 : Model) (regs1 : bvmap 5 word),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONDATA_CID, pos) :: own) ly2 S2 W2 m1 md1 (k + e) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ONDATA_S + 18208 <= a < ONDATA_S + 18216) ->
     aview segs (w_H W2) m1 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m1 a) ->
  tw_at TMAP_B (aview segs (w_H W2) m1) (odac_wa B1 r) ->
  od_regs_s regs regs1 fp sp1 F ->
  YK11.getr regs1 22 = w64 F -> YK11.getr regs1 23 = w64 now ->
  YK11.getr regs1 24 = w64 (ONDATA_S + 18160) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regs1 (Z_to_bv 64 (BASE + ODAC_P1A8)) m1 (YK11.seg_rom segs)) md1)
    (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b)).
{ intros m1 md1 regs1 HJ9 KD9 GR9 TW9 HRG9 Q22 Q23 Q24.
  pose proof HRG9 as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q25 & Q26) & Q18 & Q19 & Q20 & Q21 & Q27).
  assert (LBa : length (odac_wa B1 r) = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ TW9).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ9) as HAR9.
  set (Ba := odac_wa B1 r) in *.
  set (rx := TW.u_at Ba (TW.OFF_g_s + 18160) 8).
  set (dr := TW.u_at Ba (TW.OFF_g_s + 18176) 8).
  set (cf := TW.u_at Ba (TW.OFF_g_s + 36) 4).
  assert (Hrx : 0 <= rx < 2 ^ 64) by exact (TWL.u_at_range Ba _ 8).
  assert (Hdr : 0 <= dr < 2 ^ 64) by exact (TWL.u_at_range Ba _ 8).
  assert (Hcf : 0 <= cf < 2 ^ 32) by exact (TWL.u_at_range Ba _ 4).
  assert (HVrx : YI04.val_mem segs (mrestrict (w_H W2) m1) (ONDATA_S + 18160) 8 rx)
    by exact (tw_read_val segs _ TMAP_B Ba TW.OFF_g_s TB_g_s TW.SZ_g_s 18160 8 TMAP_B_ok TW9 TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  assert (HVdr : YI04.val_mem segs (mrestrict (w_H W2) m1) (ONDATA_S + 18176) 8 dr)
    by exact (tw_read_val segs _ TMAP_B Ba TW.OFF_g_s TB_g_s TW.SZ_g_s 18176 8 TMAP_B_ok TW9 TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  assert (HVcf : YI04.val_mem segs (mrestrict (w_H W2) m1) (ONDATA_S + 36) 4 cf)
    by exact (tw_read_val segs _ TMAP_B Ba TW.OFF_g_s TB_g_s TW.SZ_g_s 36 4 TMAP_B_ok TW9 TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  assert (HVrt : YI04.val_mem segs (mrestrict (w_H W2) m1) (fp + 28) 2 (DSpec.fr_retry b)).
  { intros t Ht. rewrite (odm_mb_eq (w_H W2) (w_H W2) mem2 m1 (fp + 28 + Z.of_nat t)).
    - exact (HV28 t Ht).
    - apply KD9; [lia|]. unfold ONDATA_S, TB_g_s, TW.SZ_g_s in *. destruct HFG as [h | h]; lia. }
  assert (HRAg9 : forall q n, ONDATA_S <= q -> q + n <= ONDATA_S + TW.SZ_g_s ->
    range_addressable (aview segs (w_H W2) m1) SHADOW_OFF q n)
    by (intros q n Hq Hn; exact (odm_ra_gs B ly2 S2 W2 m1 md1 q n HSC HAR9 Hq Hn)).
  assert (HRAf9 : range_addressable (aview segs (w_H W2) m1) SHADOW_OFF fp 64).
  { intros x Hx. destruct (HRAf2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    unfold shadow_of_addr in *. rewrite KD9; [exact Hs | |].
    - pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
      assert (x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in *. lia.
    - pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). unfold ONDATA_S, TB_g_s, SHADOW_OFF. lia. }
  assert (Hslot9 : forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W2) m1 a)
    by (intros a Ha; apply (odm_jpres B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ9); lia).
  destruct (odac_entry2a W2 regs1 m1 fp sp1 rx (DSpec.fr_retry b) Q9 Q20 Q24 Q27 Hsp1R Hsp1al
    Hfp4 Hfp8 Hfph HAPf HFG HOW Hrx Hrtr Hslot9 HVrx HVrt
    ltac:(apply HRAg9; [lia | unfold TW.SZ_g_s; lia]) HRAf9) as [HS SHOK].
  set (E := odac_E3 regs1 rx (DSpec.fr_retry b)) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply odac_env3).
  assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regs1 rr)
    by (intros n rr Hn; unfold E; apply odac_ew3_reg; exact Hn).
  assert (E33 : ew E 33 = Z_to_bv 64 rx) by (unfold E; apply odac_ew3_33).
  assert (E34 : ew E 34 = Z_to_bv 64 (DSpec.fr_retry b)) by (unfold E; apply odac_ew3_34).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat (9%bv : bv 5) eq_refl), Q9; unfold w64; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = ONDATA_S + 18160)
    by (rewrite (EE 24%nat (24%bv : bv 5) eq_refl), Q24; unfold w64; apply unsigned_lit_small;
        unfold ONDATA_S, TB_g_s; lia).
  assert (HD28 : 0 <= (fp + 28) / 8 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (SH28 : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 28) (SLit 3)) (SOff 27 0)) =
    w64 (SHADOW_OFF + (fp + 28) / 8)).
  { apply (odac_denot_shadow E 20 27 fp 28 SHADOW_OFF);
    [ rewrite (EE 20%nat (20%bv : bv 5) eq_refl), Q20; reflexivity
    | rewrite (EE 27%nat (27%bv : bv 5) eq_refl), Q27; reflexivity
    | lia | lia | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia ]. }
  assert (S28 : sv_denot E (SOff 20 28) = w64 (fp + 28))
    by (cbn [sv_denot]; rewrite (EE 20%nat (20%bv : bv 5) eq_refl), Q20; unfold w64;
        rewrite (unsigned_lit_small fp) by lia; reflexivity).
  (* +0x1a8 .. +0x1dc: the frame word, stats.rx_data, the check and the load of f + 28 *)
  pose proof HJ9 as HJ.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { odac_awr_rs. odac_awr_slot U9. odac_awr_g U24. odac_awr_0. apply awr_ok_x_nil. }
  rename HF into HFa, HFr into HFra, HG into HGa.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msA end.
  assert (KPa : forall a, 0 <= a < 2 ^ 64 ->
    ~ (sp1 + 24 <= a < sp1 + 32 \/ ONDATA_S + 18160 <= a < ONDATA_S + 18168) ->
    aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) m1 a).
  { apply (kept_of_frame _ _ _ _ _
      (fun a => sp1 + 24 <= a < sp1 + 32 \/ ONDATA_S + 18160 <= a < ONDATA_S + 18168) HFra).
    odac_win. }
  (* +0x1e0: `beqz a2` *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* no retry: to +0x240 *)
    cbn [branch_taken] in Hc.
    rewrite (odac_lhu E 34 (DSpec.fr_retry b) E34 Hrtr) in Hc.
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (POD.od_eqb0 (DSpec.fr_retry b) ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan OD_DUP.
    { odac_awr_rs. odac_awr_slot U9. odac_awr_g U24. odac_awr_0. apply awr_ok_x_nil. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end.
    assert (KPF : forall a, 0 <= a < 2 ^ 64 ->
      ~ (sp1 + 24 <= a < sp1 + 32 \/ ONDATA_S + 18160 <= a < ONDATA_S + 18168) ->
      aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) (ms_mem msA) a).
    { apply (kept_of_frame _ _ _ _ _
        (fun a => sp1 + 24 <= a < sp1 + 32 \/ ONDATA_S + 18160 <= a < ONDATA_S + 18168) HFr).
      odac_win. }
    assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a ->
      aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a).
    { intros a Ha Hn. unfold Zs in Hn.
      rewrite (KPF a Ha ltac:(intros X; apply Hn; tauto)), (KPa a Ha ltac:(intros X; apply Hn; tauto)).
      exact (KD9 a Ha ltac:(intros X; apply Hn; tauto)). }
    assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HGa (GR9 a Ha)))).
    odac_region HS 0%nat HRslot. odac_region HS 1%nat HRrxd.
    assert (Hs24 : rdword (aview segs (w_H W2) (ms_mem msF)) (sp1 + 24) = Some F).
    { apply (YF0x.val_mem_rdword (w_H W2) (ms_mem msF) (sp1 + 24) F ltac:(lia)).
      apply (can_field_of_region E _ 9 sp1 _ 24 32 24 32 24 8%N (SOff 22 0) F HRslot U9 ltac:(cbn [In]; auto));
        [| cbn; lia | cbn; lia].
      cbn [sv_denot]. rewrite (EE 22%nat (22%bv : bv 5) eq_refl), Q22, Z.add_0_r.
      unfold w64. rewrite (unsigned_lit_small F) by lia. reflexivity. }
    assert (Brx : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msF) (ONDATA_S + 18160 + Z.of_nat j) =
      Some (YO0f.le_byte (TS0.u64 (rx + 1)) 8 j)).
    { intros j Hj. replace (ONDATA_S + 18160 + Z.of_nat j) with (ONDATA_S + 18160 + 0 + Z.of_nat j) by lia.
      exact (odm_wr_bytes E (w_H W2) (ms_mem msF) 24 (ONDATA_S + 18160) 0 8 0 8 _ 0 8 (SOff 33 1)
        (TS0.u64 (rx + 1)) HRrxd U24 ltac:(cbn [In]; auto) (odac_res1 E 33 rx E33 Hrx) j Hj). }
    assert (TWE : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msF)) (ondata_w2 B1 b r now)).
    { rewrite odac_w2_eq. change (odac_wa B1 r) with Ba. rewrite (odac_wb_0 Ba b now Hc).
      apply (tw_write TMAP_B (aview segs (w_H W2) m1) _ Ba TW.OFF_g_s TB_g_s TW.SZ_g_s 18160 8 _ TMAP_B_ok
        TW9 TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
      - intros j Hj. exact (Brx j Hj).
      - intros x Hx Hn.
        assert (Hl := inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX (odm_tw_in_G x Hx)).
        unfold kLowMemEnd in Hl.
        rewrite (KPF x ltac:(lia) ltac:(unfold ONDATA_S in *; lia)).
        exact (KPa x ltac:(lia) ltac:(unfold ONDATA_S in *; lia)). }
    assert (HRG : od_regs_dup regs (ms_regs msF) fp b sp1 F).
    { unfold od_regs_dup. refine (conj _ (conj _ (conj _ (conj _ _)))).
      - odac_regs_s HS EE Q2 Q3 Q4 Q8 Q9 Q25 Q26 Q18 Q19 Q20 Q21 Q27.
      - odac_regv HS (22%bv : bv 5) ltac:(exact S28).
      - odac_keep HS EE 24%nat (24%bv : bv 5) Q24.
      - odac_regv HS (12%bv : bv 5) ltac:(exact (odac_lhu E 34 _ E34 Hrtr)).
      - odac_regv HS (17%bv : bv 5) ltac:(exact SH28). }
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_DUP)) mm rom) mdx) Q) end.
    apply (TODUP (ms_mem msF) _ (ms_regs msF));
      [exact HJ | exact KP | exact GA | exact Hs24 | exact TWE | exact HRG].
  - (* a retry *)
    cbn [branch_taken] in Hc. rewrite (odac_lhu E 34 (DSpec.fr_retry b) E34 Hrtr) in Hc.
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (POD.od_eqb0 (DSpec.fr_retry b) ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ODAC_P1E4.
    { odac_awr_rs. odac_awr_slot U9. odac_awr_g U24. odac_awr_0. apply awr_ok_x_nil. }
    rename HF into HFb, HFr into HFrb, HG into HGb.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msB end.
    assert (KPB : forall a, 0 <= a < 2 ^ 64 ->
      ~ (sp1 + 24 <= a < sp1 + 32 \/ ONDATA_S + 18160 <= a < ONDATA_S + 18168) ->
      aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) (ms_mem msA) a).
    { apply (kept_of_frame _ _ _ _ _
        (fun a => sp1 + 24 <= a < sp1 + 32 \/ ONDATA_S + 18160 <= a < ONDATA_S + 18168) HFrb).
      odac_win. }
    (* the frame word and stats.rx_data at +0x1e4 *)
    odac_region HS 0%nat HRslot. odac_region HS 1%nat HRrxd.
    assert (Hs24B : rdword (aview segs (w_H W2) (ms_mem msB)) (sp1 + 24) = Some F).
    { apply (YF0x.val_mem_rdword (w_H W2) (ms_mem msB) (sp1 + 24) F ltac:(lia)).
      apply (can_field_of_region E _ 9 sp1 _ 24 32 24 32 24 8%N (SOff 22 0) F HRslot U9 ltac:(cbn [In]; auto));
        [| cbn; lia | cbn; lia].
      cbn [sv_denot]. rewrite (EE 22%nat (22%bv : bv 5) eq_refl), Q22, Z.add_0_r.
      unfold w64. rewrite (unsigned_lit_small F) by lia. reflexivity. }
    assert (BrxB : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msB) (ONDATA_S + 18160 + Z.of_nat j) =
      Some (YO0f.le_byte (TS0.u64 (rx + 1)) 8 j)).
    { intros j Hj. replace (ONDATA_S + 18160 + Z.of_nat j) with (ONDATA_S + 18160 + 0 + Z.of_nat j) by lia.
      exact (odm_wr_bytes E (w_H W2) (ms_mem msB) 24 (ONDATA_S + 18160) 0 8 0 8 _ 0 8 (SOff 33 1)
        (TS0.u64 (rx + 1)) HRrxd U24 ltac:(cbn [In]; auto) (odac_res1 E 33 rx E33 Hrx) j Hj). }
    clear HRslot HRrxd.
    (* the registers at +0x1e4 *)
    assert (HRGB : od_regs_s regs (ms_regs msB) fp sp1 F)
      by (odac_regs_s HS EE Q2 Q3 Q4 Q8 Q9 Q25 Q26 Q18 Q19 Q20 Q21 Q27).
    assert (Y22 : YK11.getr (ms_regs msB) 22 = w64 (fp + 28)) by (odac_regv HS (22%bv : bv 5) ltac:(exact S28)).
    assert (Y23 : YK11.getr (ms_regs msB) 23 = w64 now) by (odac_keep HS EE 23%nat (23%bv : bv 5) Q23).
    assert (Y24 : YK11.getr (ms_regs msB) 24 = w64 (ONDATA_S + 18160))
      by (odac_keep HS EE 24%nat (24%bv : bv 5) Q24).
    assert (Y12 : YK11.getr (ms_regs msB) 12 = w64 (DSpec.fr_retry b))
      by (odac_regv HS (12%bv : bv 5) ltac:(exact (odac_lhu E 34 _ E34 Hrtr))).
    assert (Y17 : YK11.getr (ms_regs msB) 17 = w64 (SHADOW_OFF + (fp + 28) / 8))
      by (odac_regv HS (17%bv : bv 5) ltac:(exact SH28)).
    pose proof HRGB as ((Y2 & Y3 & Y4 & Y8 & Y9 & Y25 & Y26) & Y18 & Y19 & Y20 & Y21 & Y27).
    (* the values the retry path reads, at +0x1e4 *)
    assert (KAB : forall a, 0 <= a < 2 ^ 64 ->
      ~ (sp1 + 24 <= a < sp1 + 32 \/ ONDATA_S + 18160 <= a < ONDATA_S + 18168) ->
      aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) m1 a)
      by (intros a Ha Hn; rewrite (KPB a Ha Hn); exact (KPa a Ha Hn)).
    assert (HVdrB : YI04.val_mem segs (mrestrict (w_H W2) (ms_mem msB)) (ONDATA_S + 18176) 8 dr).
    { intros t Ht. rewrite (odm_mb_eq (w_H W2) (w_H W2) m1 (ms_mem msB) (ONDATA_S + 18176 + Z.of_nat t)).
      - exact (HVdr t Ht).
      - apply KAB; unfold ONDATA_S, TB_g_s in *; lia. }
    assert (HVcfB : YI04.val_mem segs (mrestrict (w_H W2) (ms_mem msB)) (ONDATA_S + 36) 4 cf).
    { intros t Ht. rewrite (odm_mb_eq (w_H W2) (w_H W2) m1 (ms_mem msB) (ONDATA_S + 36 + Z.of_nat t)).
      - exact (HVcf t Ht).
      - apply KAB; unfold ONDATA_S, TB_g_s in *; lia. }
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARB.
    pmkst HS.
    lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ODAC_P1E4)) mm rom) mdx) Q) end.
    clear HS SHOK.
    destruct (odac_entry2b W2 (ms_regs msB) (ms_mem msB) dr cf Y19 Y24 Y27 Hdr Hcf HVdrB HVcfB
      (odm_ra_gs B ly2 S2 W2 (ms_mem msB) _ (ONDATA_S + 18176) 8 HSC HARB ltac:(lia) ltac:(unfold TW.SZ_g_s; lia))
      (odm_ra_gs B ly2 S2 W2 (ms_mem msB) _ (ONDATA_S + 36) 164 HSC HARB ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)))
      as [HS SHOK].
    set (EB := odac_E3 (ms_regs msB) dr cf) in HS, SHOK.
    assert (HEIB : img_env VAL A_LIM EB) by (unfold EB; apply odac_env3).
    assert (EEB : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew EB n = YK11.getr (ms_regs msB) rr)
      by (intros n rr Hn; unfold EB; apply odac_ew3_reg; exact Hn).
    assert (EB33 : ew EB 33 = Z_to_bv 64 dr) by (unfold EB; apply odac_ew3_33).
    assert (EB34 : ew EB 34 = Z_to_bv 64 cf) by (unfold EB; apply odac_ew3_34).
    assert (UB19 : bv_unsigned (ew EB 19) = ONDATA_S)
      by (rewrite (EEB 19%nat (19%bv : bv 5) eq_refl), Y19; unfold w64; apply unsigned_lit_small;
          unfold ONDATA_S, TB_g_s; lia).
    assert (UB24 : bv_unsigned (ew EB 24) = ONDATA_S + 18160)
      by (rewrite (EEB 24%nat (24%bv : bv 5) eq_refl), Y24; unfold w64; apply unsigned_lit_small;
          unfold ONDATA_S, TB_g_s; lia).
    (* +0x1e4 .. +0x23c: stats.rx_desk_retries, the checks of s + 36 and s + 192, the backoff *)
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan OD_DUP.
    { odac_awr_rs. odac_awr_g UB24. odac_awr_0. odac_awr_g UB19. apply awr_ok_x_nil. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end.
    assert (KPC : forall a, 0 <= a < 2 ^ 64 ->
      ~ (ONDATA_S + 18176 <= a < ONDATA_S + 18184 \/ ONDATA_S + 192 <= a < ONDATA_S + 200) ->
      aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) (ms_mem msB) a).
    { apply (kept_of_frame _ _ _ _ _
        (fun a => ONDATA_S + 18176 <= a < ONDATA_S + 18184 \/ ONDATA_S + 192 <= a < ONDATA_S + 200) HFr).
      odac_win. }
    assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HGb
            (apresent_grows _ _ _ a HGa (GR9 a Ha))))).
    assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a ->
      aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a).
    { intros a Ha Hn. unfold Zs in Hn.
      rewrite (KPC a Ha ltac:(intros X; apply Hn; tauto)), (KPB a Ha ltac:(intros X; apply Hn; tauto)),
        (KPa a Ha ltac:(intros X; apply Hn; tauto)).
      exact (KD9 a Ha ltac:(intros X; apply Hn; tauto)). }
    assert (Hs24 : rdword (aview segs (w_H W2) (ms_mem msF)) (sp1 + 24) = Some F).
    { apply (YF0x.rdword_ext (aview segs (w_H W2) (ms_mem msB)) (aview segs (w_H W2) (ms_mem msF)) (sp1 + 24) F);
      [|exact Hs24B].
      intros i Hi. apply KPC; [lia|]. unfold ONDATA_S, TB_g_s. lia. }
    odac_region HS 0%nat HRdrt. odac_region HS 2%nat HRbku.
    assert (Bdr : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msF) (ONDATA_S + 18176 + Z.of_nat j) =
      Some (YO0f.le_byte (TS0.u64 (dr + 1)) 8 j)).
    { intros j Hj. replace (ONDATA_S + 18176 + Z.of_nat j) with (ONDATA_S + 18160 + 16 + Z.of_nat j) by lia.
      exact (odm_wr_bytes EB (w_H W2) (ms_mem msF) 24 (ONDATA_S + 18160) 16 24 16 24 _ 16 8 (SOff 33 1)
        (TS0.u64 (dr + 1)) HRdrt UB24 ltac:(cbn [In]; auto) (odac_res1 EB 33 dr EB33 Hdr) j Hj). }
    assert (Bbk : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msF) (ONDATA_S + 192 + Z.of_nat j) =
      Some (YO0f.le_byte (TS0.u64 (now + cf * 1000)) 8 j)).
    { intros j Hj.
      exact (odm_wr_bytes EB (w_H W2) (ms_mem msF) 19 ONDATA_S 192 200 192 200 _ 192 8
        (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff 34 0)) (SLit 1000)) (SOff 23 0))
        (TS0.u64 (now + cf * 1000)) HRbku UB19 ltac:(cbn [In]; auto)
        (odac_bku_val EB 34 23 cf now EB34 ltac:(rewrite (EEB 23%nat (23%bv : bv 5) eq_refl), Y23; reflexivity)
          Hcf Hnow) j Hj). }
    assert (Brx : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msF) (ONDATA_S + 18160 + Z.of_nat j) =
      Some (YO0f.le_byte (TS0.u64 (rx + 1)) 8 j)).
    { intros j Hj. rewrite (KPC (ONDATA_S + 18160 + Z.of_nat j) ltac:(unfold ONDATA_S, TB_g_s; lia)
        ltac:(unfold ONDATA_S, TB_g_s; lia)).
      exact (BrxB j Hj). }
    assert (TWE : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msF)) (ondata_w2 B1 b r now)).
    { rewrite odac_w2_eq. change (odac_wa B1 r) with Ba. rewrite (odac_wb_1 Ba b now LBa Hc Hcf).
      set (rd := aview segs (w_H W2) m1). set (rd' := aview segs (w_H W2) (ms_mem msF)).
      assert (T0 : tw_at TMAP_B (fun x => if ((odac_inb 192 8 x || odac_inb 18176 8 x) || odac_inb 18160 8 x)%bool
        then rd x else rd' x) Ba).
      { apply (tw_kept TMAP_B rd); [exact TW9|]. intros x Hx. cbv beta.
        destruct ((odac_inb 192 8 x || odac_inb 18176 8 x) || odac_inb 18160 8 x)%bool eqn:EZ; [reflexivity|].
        apply orb_false_iff in EZ as [EZ E3]. apply orb_false_iff in EZ as [E1 E2].
        apply odac_inb_false in E1. apply odac_inb_false in E2. apply odac_inb_false in E3.
        assert (Hl := inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX (odm_tw_in_G x Hx)).
        unfold kLowMemEnd in Hl. unfold rd, rd'.
        rewrite (KPC x ltac:(lia) ltac:(lia)), (KPB x ltac:(lia) ltac:(lia)). exact (KPa x ltac:(lia) ltac:(lia)). }
      pose proof (odac_tws rd rd' (fun x => (odac_inb 192 8 x || odac_inb 18176 8 x)%bool) Ba 18160 8 _ T0
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) Brx
        ltac:(intros j Hj; cbv beta; rewrite !odac_inb_out by lia; reflexivity)) as T1.
      cbv beta in T1.
      pose proof (odac_tws rd rd' (odac_inb 192 8) _ 18176 8 _ T1 ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) Bdr
        ltac:(intros j Hj; rewrite odac_inb_out by lia; reflexivity)) as T2.
      pose proof (odac_tws rd rd' (fun _ => false) _ 192 8 _ T2 ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) Bbk
        ltac:(intros j Hj; reflexivity)) as T3.
      apply (tw_kept TMAP_B _ rd' _ T3). intros x _. reflexivity. }
    assert (HRG : od_regs_dup regs (ms_regs msF) fp b sp1 F).
    { unfold od_regs_dup. refine (conj _ (conj _ (conj _ (conj _ _)))).
      - odac_regs_s HS EEB Y2 Y3 Y4 Y8 Y9 Y25 Y26 Y18 Y19 Y20 Y21 Y27.
      - odac_keep HS EEB 22%nat (22%bv : bv 5) Y22.
      - odac_keep HS EEB 24%nat (24%bv : bv 5) Y24.
      - odac_keep HS EEB 12%nat (12%bv : bv 5) Y12.
      - odac_keep HS EEB 17%nat (17%bv : bv 5) Y17. }
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_DUP)) mm rom) mdx) Q) end.
    apply (TODUP (ms_mem msF) _ (ms_regs msF));
      [exact HJ | exact KP | exact GA | exact Hs24 | exact TWE | exact HRG]. }
(* ---- +0x174 .. +0x178: `andi a1, s3, 7`, then `beqz a0` ---- *)
pose proof (odac_entry1 W2 regs2 mem2 R19) as HS.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (odac_E1 regs2) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI1 : img_env VAL A_LIM (odac_E1 regs2)) by apply odac_env1.
assert (EE1 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (odac_E1 regs2) n = YK11.getr regs2 rr)
  by (intros n rr Hn; apply odac_ew1_reg; exact Hn).
assert (D10 : sv_denot (odac_E1 regs2) (SOff 10 0) = Z_to_bv 64 r)
  by (cbn [sv_denot]; rewrite (EE1 10%nat (10%bv : bv 5) eq_refl), R10, Z.add_0_r; unfold w64;
      apply Z_to_bv_bv_unsigned).
pose proof HJ1 as HJ.
paj_run_tok RUN HS HJ SHOK ODAC_B0.
{ odac_awr_rs. apply awr_ok_x_nil. }
rename HF into HFz, HFr into HFr0, HG into HG0.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms0 end.
assert (KD0 : forall a, aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) mem2 a).
{ intros a. rewrite (aview_wrap64 segs _ (ms_mem ms0) a), (aview_wrap64 segs _ mem2 a).
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
  apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr0); [odac_win | lia | intros []]. }
psrr_branch_tok RUN BR HS SHOK ODAC_B0.
- (* r = 0: +0x184 `bnez a1` (a1 = 0), then +0x188 .. +0x1a4, the checked increment of stats.tx_acks *)
  cbn [branch_taken] in Hc.
  rewrite D10 in Hc. change (sv_denot (odac_E1 regs2) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (POD.od_eqb0 r Hrr) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hr0.
  paj_run_to_tok RUNTO HS HJ SHOK ODAC_B0 ODAC_P188.
  { odac_awr_rs. apply awr_ok_x_nil. }
  rename HF into HF1, HFr into HFr1, HG into HG1.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msA end.
  assert (KDA : forall a, aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a).
  { intros a. rewrite <- (KD0 a). rewrite (aview_wrap64 segs _ (ms_mem msA) a), (aview_wrap64 segs _ (ms_mem ms0) a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr1); [odac_win | lia | intros []]. }
  assert (HRGA : od_regs_s regs (ms_regs msA) fp sp1 F)
    by (odac_regs_s HS EE1 R2 R3 R4 R8 R9 R25 R26 R18 R19 R20 R21 R27).
  assert (X22 : YK11.getr (ms_regs msA) 22 = w64 F) by (odac_keep HS EE1 22%nat (22%bv : bv 5) R22).
  assert (X23 : YK11.getr (ms_regs msA) 23 = w64 now) by (odac_keep HS EE1 23%nat (23%bv : bv 5) R23).
  assert (X24 : YK11.getr (ms_regs msA) 24 = w64 (ONDATA_S + 18160))
    by (odac_keep HS EE1 24%nat (24%bv : bv 5) R24).
  pose proof HRGA as ((X2 & X3 & X4 & X8 & X9 & X25 & X26) & X18 & X19 & X20 & X21 & X27).
  set (tx := TW.u_at B1 (TW.OFF_g_s + 18208) 8).
  assert (Htx : 0 <= tx < 2 ^ 64) by exact (TWL.u_at_range B1 _ 8).
  assert (HVtx : YI04.val_mem segs (mrestrict (w_H W2) (ms_mem msA)) (ONDATA_S + 18208) 8 tx).
  { intros t Ht. rewrite (odm_mb_eq (w_H W2) (w_H W2) mem2 (ms_mem msA) (ONDATA_S + 18208 + Z.of_nat t) (KDA _)).
    exact (tw_read_val segs _ TMAP_B B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 18208 8 TMAP_B_ok HTW1 TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) t Ht). }
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARA.
  pmkst HS.
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ODAC_P188)) mm rom) mdx) Q) end.
  clear HS SHOK.
  destruct (odac_entry1b W2 (ms_regs msA) (ms_mem msA) tx X24 X27 Htx HVtx
    (odm_ra_gs B ly2 S2 W2 (ms_mem msA) _ (ONDATA_S + 18208) 8 HSC HARA ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)))
    as [HS SHOK].
  set (E1 := odac_E1b (ms_regs msA) tx) in HS, SHOK.
  assert (HEI1b : img_env VAL A_LIM E1) by (unfold E1; apply odac_env1b).
  assert (EE1b : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E1 n = YK11.getr (ms_regs msA) rr)
    by (intros n rr Hn; unfold E1; apply odac_ew1b_reg; exact Hn).
  assert (E133 : ew E1 33 = Z_to_bv 64 tx) by (unfold E1; apply odac_ew1b_33).
  assert (U24a : bv_unsigned (ew E1 24) = ONDATA_S + 18160)
    by (rewrite (EE1b 24%nat (24%bv : bv 5) eq_refl), X24; unfold w64; apply unsigned_lit_small;
        unfold ONDATA_S, TB_g_s; lia).
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ODAC_P1A8.
  { odac_awr_rs. odac_awr_g U24a. apply awr_ok_x_nil. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms9 end.
  assert (KP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (ONDATA_S + 18208 <= a < ONDATA_S + 18216) ->
    aview segs (w_H W2) (ms_mem ms9) a = aview segs (w_H W2) (ms_mem msA) a).
  { apply (kept_of_frame _ _ _ _ _ (fun a => ONDATA_S + 18208 <= a < ONDATA_S + 18216) HFr). odac_win. }
  odac_region HS 0%nat HRtx.
  assert (Btx : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem ms9) (ONDATA_S + 18208 + Z.of_nat j) =
    Some (YO0f.le_byte (TS0.u64 (tx + 1)) 8 j)).
  { intros j Hj. replace (ONDATA_S + 18208 + Z.of_nat j) with (ONDATA_S + 18160 + 48 + Z.of_nat j) by lia.
    exact (odm_wr_bytes E1 (w_H W2) (ms_mem ms9) 24 (ONDATA_S + 18160) 48 56 48 56 _ 48 8 (SOff 33 1)
      (TS0.u64 (tx + 1)) HRtx U24a ltac:(cbn [In]; auto) (odac_res1 E1 33 tx E133 Htx) j Hj). }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ODAC_P1A8)) mm rom) mdx) Q) end.
  apply (J1A8 (ms_mem ms9) _ (ms_regs ms9)).
  + exact HJ.
  + intros a Ha Hn. rewrite (KP1 a Ha Hn). exact (KDA a).
  + intros a Ha. exact (apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG1 (apresent_grows _ _ _ a HG0 Ha))).
  + rewrite (odac_wa_0 B1 r Hr0).
    apply (tw_write TMAP_B (aview segs (w_H W2) mem2) _ B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 18208 8 _ TMAP_B_ok
      HTW1 TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    * intros j Hj. exact (Btx j Hj).
    * intros x Hx Hn.
      assert (Hl := inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX (odm_tw_in_G x Hx)).
      unfold kLowMemEnd in Hl.
      rewrite (KP1 x ltac:(lia) ltac:(unfold ONDATA_S in *; lia)). exact (KDA x).
  + odac_regs_s HS EE1b X2 X3 X4 X8 X9 X25 X26 X18 X19 X20 X21 X27.
  + odac_keep HS EE1b 22%nat (22%bv : bv 5) X22.
  + odac_keep HS EE1b 23%nat (23%bv : bv 5) X23.
  + odac_keep HS EE1b 24%nat (24%bv : bv 5) X24.
- (* r <> 0: +0x17c `beqz a1` (a1 = 0), to +0x1a8 *)
  cbn [branch_taken] in Hc.
  rewrite D10 in Hc. change (sv_denot (odac_E1 regs2) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (POD.od_eqb0 r Hrr) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hr0.
  paj_run_to_tok RUNTO HS HJ SHOK ODAC_B0 ODAC_P1A8.
  { odac_awr_rs. apply awr_ok_x_nil. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms9 end.
  assert (KD : forall a, aview segs (w_H W2) (ms_mem ms9) a = aview segs (w_H W2) mem2 a).
  { intros a. rewrite <- (KD0 a). rewrite (aview_wrap64 segs _ (ms_mem ms9) a), (aview_wrap64 segs _ (ms_mem ms0) a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [odac_win | lia | intros []]. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ODAC_P1A8)) mm rom) mdx) Q) end.
  apply (J1A8 (ms_mem ms9) _ (ms_regs ms9)).
  + exact HJ.
  + intros a _ _. exact (KD a).
  + intros a Ha. exact (apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG0 Ha)).
  + rewrite (odac_wa_n0 B1 r Hr0).
    apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW1 | intros x _; exact (KD x)].
  + odac_regs_s HS EE1 R2 R3 R4 R8 R9 R25 R26 R18 R19 R20 R21 R27.
  + odac_keep HS EE1 22%nat (22%bv : bv 5) R22.
  + odac_keep HS EE1 23%nat (23%bv : bv 5) R23.
  + odac_keep HS EE1 24%nat (24%bv : bv 5) R24.
Qed.

End acks.

Theorem od_acks : forall fx rc B MT, @od_acks_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@odac_acks fx rc B MT). Qed.

Print Assumptions od_acks.
