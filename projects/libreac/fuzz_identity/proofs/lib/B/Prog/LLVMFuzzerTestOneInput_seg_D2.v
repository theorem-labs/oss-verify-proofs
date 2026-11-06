(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-157, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* seg_D2 of the B walk of LLVMFuzzerTestOneInput (fuzz_identity.asan-ubsan 0x80774): from inv_D1_end at
   +0x630 (0x80da4) to the four exits of the switch, inv_caseV (+0x888), inv_caseM (+0xb44), inv_caseF (+0x730)
   and inv_ignored (+0x7b4). The statement seg_D2_stmt is the boundary layer's (LLVMFuzzerTestOneInput_inv.v).

   The code: 0x80da4 compares the two ingest results (x26 = x20 = rec_r, so r2 = r); then same_id(again, id):
   the 16-bit fw value (+0), has_fw (+2), the bcmp wrapper on model_name (17 bytes at +3, 0x80de8), has_model_name
   (+20), major / minor / patch (+22, +24, +26), the bcmp wrapper on reac_version_raw (8 bytes at +28, 0x80e60)
   and has_reac_version (+36). `again` and `id` both hold m_id g (S i), so every compare is equal and both calls
   return 0; the abort branches to 0x82614 are not taken. The switch (0x80e84..0x80ea0): rec_r = 0 goes to the
   ignored-record path; rec_r = 1 holds only for the three modelled addresses (ING in RcIdentModel), which go to
   the three cases, so the default `j 82614` at 0x80ea0 is not reached.

   The walk runs the engine of IdentBPaLib.v (paj_run_tok) on a symbolic state of two read-only regions: the
   machine frame (base s1, the seven slots loaded) and the side-stack frame (base SF, the seven fields of
   `again` and of `id`, the same atoms for both). It is split at the two calls: d2_p1 (to the return of the
   first call), d2_p2 (to the return of the second), d2_p3 (to the exits). d2_call is the call (aj_bcmp_at under
   the walk's journal), d2_core carries every fact of the exits across the calls (they write only their window
   [mf - 2 * ESTACK, mf); the runs write nothing). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

(* ---- the symbolic state of the walk -------------------------------------------------------------------- *)
(* Byte k and the 16-bit little-endian half at k of a byte list. *)
Definition d2_b (l : list byte) (k : nat) : Z := bv_unsigned (nth k l (Z_to_bv 8 0)).
Definition d2_h (l : list byte) (k : nat) : Z := d2_b l k + 256 * d2_b l (S k).
(* The fields the walk reads of `again` and of `id`, which hold the same bytes (m_id g (S i)): the 16-bit
   firmware value (+0), has_fw (+2), has_model_name (+20), major (+22), minor (+24), patch (+26), has_ver (+36). *)
Definition d2_flds (l : list byte) : list Z :=
[d2_h l 0; d2_b l 2; d2_b l 20; d2_h l 22; d2_h l 24; d2_h l 26; d2_b l 36].
(* Atoms 32 .. 39: the frame address SF, then the seven field values. *)
Definition d2_extra (sf : Z) (l : list byte) : list word := map (Z_to_bv 64) (sf :: d2_flds l).
Definition E_D2 (regs : bvmap 5 word) (sf : Z) (l : list byte) : env := Eimg (Ereg regs (d2_extra sf l)).
(* The machine frame (base s1 = x9): the seven slots the walk loads. *)
Definition d2_mf_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 80 192 0 0
[YP09.mkChunk 80 (CVal 8 (SOff 32 140)); YP09.mkChunk 88 (CVal 8 (SOff 32 115));
 YP09.mkChunk 104 (CVal 8 (SOff 32 380)); YP09.mkChunk 136 (CVal 8 (SOff 32 355));
 YP09.mkChunk 168 (CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk 176 (CVal 8 (SOff 32 112));
 YP09.mkChunk 184 (CVal 8 (SOff 32 352))].
(* The seven fields of a 38-byte identity at frame offset o. *)
Definition d2_obj_chunks (o : Z) : list YP09.chunk :=
[YP09.mkChunk o (CVal 2 (SOff 33 0)); YP09.mkChunk (o + 2) (CVal 1 (SOff 34 0));
 YP09.mkChunk (o + 20) (CVal 1 (SOff 35 0)); YP09.mkChunk (o + 22) (CVal 2 (SOff 36 0));
 YP09.mkChunk (o + 24) (CVal 2 (SOff 37 0)); YP09.mkChunk (o + 26) (CVal 2 (SOff 38 0));
 YP09.mkChunk (o + 36) (CVal 1 (SOff 39 0))].
(* The side-stack frame (base SF = atom 32): `again` at +112 and `id` at +352, both read-only here. *)
Definition d2_sf_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 112 390 0 0 (d2_obj_chunks 112 ++ d2_obj_chunks 352).
Definition d2_rs : smem := [d2_mf_region; d2_sf_region].
Definition ss_D2 (pc : Z) : sstate := mkSS pc sr_atoms d2_rs None (mkFacts [] [] []).
Definition Bx_D2 : sv := SLit SHADOW_OFF.
Definition Bspan_D2 : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma d2_b_range : forall l k, 0 <= d2_b l k < 256.
Proof. intros l k. unfold d2_b. pose proof (bv_unsigned_in_range 8 (nth k l (Z_to_bv 8 0))) as H. exact H. Qed.
Lemma d2_h_range : forall l k, 0 <= d2_h l k < 65536.
Proof. intros l k. unfold d2_h. pose proof (d2_b_range l k). pose proof (d2_b_range l (S k)). lia. Qed.
Lemma d2_val1 : forall (W : world SEGS) m a l k, bytes_at8 W m a l -> (k < length l)%nat ->
val_mem SEGS (rd W m) (a + Z.of_nat k) 1 (d2_b l k).
Proof.
intros W m a l k H Hk. unfold bytes_at8, garr8 in H. rewrite length_map in H.
destruct (H k Hk) as [Hv _]. unfold d2_b. rewrite <- map_nth. exact Hv.
Qed.
Lemma d2_le1 : forall b, 0 <= b < 256 -> YO0f.le_byte b 1 0 = b.
Proof.
intros b Hb. unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small b 256) by lia. rewrite (Z.mod_small b 256) by lia. reflexivity.
Qed.
Lemma d2_le2 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
YO0f.le_byte (b0 + 256 * b1) 2 0 = b0 /\ YO0f.le_byte (b0 + 256 * b1) 2 1 = b1.
Proof.
intros b0 b1 R0 R1. unfold YO0f.le_byte. replace (8 * Z.of_nat 2) with 16 by reflexivity.
replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
change (2 ^ 16) with 65536. rewrite (Z.mod_small (b0 + 256 * b1) 65536) by lia.
rewrite Z.shiftr_0_r, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace (b0 + 256 * b1) with (b0 + b1 * 256) by ring. rewrite Z_mod_plus_full, Z.div_add by lia.
rewrite (Z.div_small b0 256), Z.add_0_l by lia. split; apply Z.mod_small; lia.
Qed.
Lemma d2_val2 : forall (m : word -> option byte) a b0 b1, val_mem SEGS m a 1 b0 -> val_mem SEGS m (a + 1) 1 b1 ->
0 <= b0 < 256 -> 0 <= b1 < 256 -> val_mem SEGS m a 2 (b0 + 256 * b1).
Proof.
intros m a b0 b1 H0 H1 R0 R1 k Hk. destruct (d2_le2 b0 b1 R0 R1) as [E0 E1].
destruct k as [|[|k]]; [| | lia].
- rewrite E0. specialize (H0 0%nat ltac:(lia)). rewrite d2_le1 in H0 by exact R0. exact H0.
- rewrite E1. specialize (H1 0%nat ltac:(lia)). rewrite d2_le1 in H1 by exact R1.
replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia. exact H1.
Qed.
Lemma d2_valh : forall (W : world SEGS) m a l k, bytes_at8 W m a l -> (S k < length l)%nat ->
val_mem SEGS (rd W m) (a + Z.of_nat k) 2 (d2_h l k).
Proof.
intros W m a l k H Hk. unfold d2_h. apply d2_val2; [apply d2_val1; [exact H | lia] | | apply d2_b_range | apply d2_b_range].
replace (a + Z.of_nat k + 1) with (a + Z.of_nat (S k)) by lia. apply d2_val1; [exact H | lia].
Qed.
Lemma d2_ew_extra : forall regs sf l j, (j < 8)%nat ->
ew (E_D2 regs sf l) (32 + j) = Z_to_bv 64 (nth j (sf :: d2_flds l) 0).
Proof.
intros regs sf l j Hj. unfold E_D2. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
unfold d2_extra. apply map_nth.
Qed.

Lemma d2_chunk_atom : forall E m base off (w : N) (n : nat) v, ew E n = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> val_mem SEGS m (base + off) (N.to_nat w) v ->
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w (SOff n 0))).
Proof.
intros E m base off w n v Hn Hv Hw H. apply (chunk_ok_val SEGS E m base off w (SOff n 0) v); [|exact Hv|exact Hw|exact H].
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma d2_chunk_ptr : forall E m base off (n : nat) s c, ew E n = Z_to_bv 64 s ->
0 <= s -> 0 <= c -> s + c < 2 ^ 64 -> val_mem SEGS m (base + off) 8 (s + c) ->
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 (SOff n c))).
Proof.
intros E m base off n s c Hn Hs Hc Hsc H. apply (chunk_ok_val SEGS E m base off 8 (SOff n c) (s + c)); [| |lia|exact H].
- cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
Qed.
(* The symbolic state at slot pc from what the walk carries: s1 = mf, the machine frame's seven slots, and the
   bytes of `again` and `id`. *)
Lemma d2_entry : forall (g : ectx) pos mf i (W : world SEGS) regs mem pc,
getr regs 9 = w64 mf -> 0 <= mf -> mf + 192 <= 2 ^ 64 -> 0 <= SFa g pos -> SFa g pos + 1024 <= mf ->
mf_fixed g pos mf W mem -> mf_again g pos mf W mem -> mf_id g pos mf W mem ->
val_mem SEGS (rd W mem) (mf + 168) 8 SHADOW_OFF ->
bytes_at8 W mem (SFa g pos + V_again) (m_id g (S i)) ->
bytes_at8 W mem (SFa g pos + V_id) (m_id g (S i)) ->
st_ok_pi SEGS VAL (E_D2 regs (SFa g pos) (m_id g (S i))) (ss_D2 pc)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros g pos mf i W regs mem pc H9 Hmf0 Hmf1 Hsf0 Hsf1 Hfix Hag Hid H168 Bag Bid.
assert (Hl : length (m_id g (S i)) = 38%nat) by (unfold m_id; apply SlotModel.rec_id_length).
destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
unfold mf_again in Hag. unfold mf_id in Hid.
set (sf := SFa g pos) in *. set (l := m_id g (S i)) in *.
set (E := E_D2 regs sf l).
assert (E9 : ew E 9 = getr regs 9) by exact (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl).
assert (E32 : ew E 32 = Z_to_bv 64 sf) by exact (d2_ew_extra regs sf l 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (d2_h l 0)) by exact (d2_ew_extra regs sf l 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (d2_b l 2)) by exact (d2_ew_extra regs sf l 2 ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (d2_b l 20)) by exact (d2_ew_extra regs sf l 3 ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (d2_h l 22)) by exact (d2_ew_extra regs sf l 4 ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 (d2_h l 24)) by exact (d2_ew_extra regs sf l 5 ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 (d2_h l 26)) by exact (d2_ew_extra regs sf l 6 ltac:(lia)).
assert (E39 : ew E 39 = Z_to_bv 64 (d2_b l 36)) by exact (d2_ew_extra regs sf l 7 ltac:(lia)).
assert (VB9 : base_val E (Some 9%nat) = mf) by (cbn [base_val]; rewrite E9, H9; unfold w64; apply unsigned_lit_small; lia).
assert (VB32 : base_val E (Some 32%nat) = sf) by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; lia).
assert (C8 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64) by reflexivity.
assert (C2 : 2 ^ (8 * Z.of_N 2) = 65536) by reflexivity.
assert (C1 : 2 ^ (8 * Z.of_N 1) = 256) by reflexivity.
rewrite restrict_mkst_fx. unfold ss_D2. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold d2_rs, d2_mf_region, d2_sf_region, d2_obj_chunks.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks app].
+ rewrite VB9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (d2_chunk_ptr E _ mf 80 32 sf 140 E32); [lia|lia|lia|]. replace (sf + 140) with (sf + V_again + 28) by (unfold V_again; lia). exact F80.
* apply (d2_chunk_ptr E _ mf 88 32 sf 115 E32); [lia|lia|lia|]. replace (sf + 115) with (sf + V_again + 3) by (unfold V_again; lia). exact F88.
* apply (d2_chunk_ptr E _ mf 104 32 sf 380 E32); [lia|lia|lia|]. replace (sf + 380) with (sf + V_id + 28) by (unfold V_id; lia). exact F104.
* apply (d2_chunk_ptr E _ mf 136 32 sf 355 E32); [lia|lia|lia|]. replace (sf + 355) with (sf + V_id + 3) by (unfold V_id; lia). exact F136.
* apply (chunk_ok_val SEGS E _ mf 168 8 (SLit SHADOW_OFF) SHADOW_OFF); [reflexivity | rewrite C8; unfold SHADOW_OFF; lia | lia | exact H168].
* apply (d2_chunk_ptr E _ mf 176 32 sf 112 E32); [lia|lia|lia|]. replace (sf + 112) with (sf + V_again) by (unfold V_again; lia). exact Hag.
* apply (d2_chunk_ptr E _ mf 184 32 sf 352 E32); [lia|lia|lia|]. replace (sf + 352) with (sf + V_id) by (unfold V_id; lia). exact Hid.
+ rewrite VB32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
pose proof (d2_h_range l 0) as R0. pose proof (d2_b_range l 2) as R2. pose proof (d2_b_range l 20) as R20.
pose proof (d2_h_range l 22) as R22. pose proof (d2_h_range l 24) as R24. pose proof (d2_h_range l 26) as R26.
pose proof (d2_b_range l 36) as R36.
repeat apply Forall_cons; try apply Forall_nil.
* apply (d2_chunk_atom E _ sf 112 2 33 _ E33); [rewrite C2; lia | lia |].
replace (sf + 112) with (sf + V_again + Z.of_nat 0) by (unfold V_again; lia). exact (d2_valh W mem _ l 0 Bag ltac:(lia)).
* apply (d2_chunk_atom E _ sf (112 + 2) 1 34 _ E34); [rewrite C1; lia | lia |].
replace (sf + (112 + 2)) with (sf + V_again + Z.of_nat 2) by (unfold V_again; lia). exact (d2_val1 W mem _ l 2 Bag ltac:(lia)).
* apply (d2_chunk_atom E _ sf (112 + 20) 1 35 _ E35); [rewrite C1; lia | lia |].
replace (sf + (112 + 20)) with (sf + V_again + Z.of_nat 20) by (unfold V_again; lia). exact (d2_val1 W mem _ l 20 Bag ltac:(lia)).
* apply (d2_chunk_atom E _ sf (112 + 22) 2 36 _ E36); [rewrite C2; lia | lia |].
replace (sf + (112 + 22)) with (sf + V_again + Z.of_nat 22) by (unfold V_again; lia). exact (d2_valh W mem _ l 22 Bag ltac:(lia)).
* apply (d2_chunk_atom E _ sf (112 + 24) 2 37 _ E37); [rewrite C2; lia | lia |].
replace (sf + (112 + 24)) with (sf + V_again + Z.of_nat 24) by (unfold V_again; lia). exact (d2_valh W mem _ l 24 Bag ltac:(lia)).
* apply (d2_chunk_atom E _ sf (112 + 26) 2 38 _ E38); [rewrite C2; lia | lia |].
replace (sf + (112 + 26)) with (sf + V_again + Z.of_nat 26) by (unfold V_again; lia). exact (d2_valh W mem _ l 26 Bag ltac:(lia)).
* apply (d2_chunk_atom E _ sf (112 + 36) 1 39 _ E39); [rewrite C1; lia | lia |].
replace (sf + (112 + 36)) with (sf + V_again + Z.of_nat 36) by (unfold V_again; lia). exact (d2_val1 W mem _ l 36 Bag ltac:(lia)).
* apply (d2_chunk_atom E _ sf 352 2 33 _ E33); [rewrite C2; lia | lia |].
replace (sf + 352) with (sf + V_id + Z.of_nat 0) by (unfold V_id; lia). exact (d2_valh W mem _ l 0 Bid ltac:(lia)).
* apply (d2_chunk_atom E _ sf (352 + 2) 1 34 _ E34); [rewrite C1; lia | lia |].
replace (sf + (352 + 2)) with (sf + V_id + Z.of_nat 2) by (unfold V_id; lia). exact (d2_val1 W mem _ l 2 Bid ltac:(lia)).
* apply (d2_chunk_atom E _ sf (352 + 20) 1 35 _ E35); [rewrite C1; lia | lia |].
replace (sf + (352 + 20)) with (sf + V_id + Z.of_nat 20) by (unfold V_id; lia). exact (d2_val1 W mem _ l 20 Bid ltac:(lia)).
* apply (d2_chunk_atom E _ sf (352 + 22) 2 36 _ E36); [rewrite C2; lia | lia |].
replace (sf + (352 + 22)) with (sf + V_id + Z.of_nat 22) by (unfold V_id; lia). exact (d2_valh W mem _ l 22 Bid ltac:(lia)).
* apply (d2_chunk_atom E _ sf (352 + 24) 2 37 _ E37); [rewrite C2; lia | lia |].
replace (sf + (352 + 24)) with (sf + V_id + Z.of_nat 24) by (unfold V_id; lia). exact (d2_valh W mem _ l 24 Bid ltac:(lia)).
* apply (d2_chunk_atom E _ sf (352 + 26) 2 38 _ E38); [rewrite C2; lia | lia |].
replace (sf + (352 + 26)) with (sf + V_id + Z.of_nat 26) by (unfold V_id; lia). exact (d2_valh W mem _ l 26 Bid ltac:(lia)).
* apply (d2_chunk_atom E _ sf (352 + 36) 1 39 _ E39); [rewrite C1; lia | lia |].
replace (sf + (352 + 36)) with (sf + V_id + Z.of_nat 36) by (unfold V_id; lia). exact (d2_val1 W mem _ l 36 Bid ltac:(lia)).
- unfold d2_rs. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [d2_mf_region d2_sf_region YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB9, VB32.
split; [split; [right; lia | exact I] | split; exact I].
- cbn. repeat split.
Qed.

(* ---- what a call keeps ------------------------------------------------------------------------------------ *)
(* The walk's two calls (the bcmp wrapper, at sp = mf) write only their window [mf - 2 * ESTACK, mf); a run of the
   walk writes nothing. So every byte outside the window keeps its view. *)
Definition d2_keep (W : world SEGS) (mf : Z) (m0 m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.
Lemma d2_keep_refl : forall W mf m, d2_keep W mf m m.
Proof. intros W mf m a _ _. reflexivity. Qed.
Lemma d2_keep_trans : forall W mf m0 m1 m2, d2_keep W mf m0 m1 -> d2_keep W mf m1 m2 -> d2_keep W mf m0 m2.
Proof. intros W mf m0 m1 m2 H1 H2 a Ha Hw. rewrite (H2 a Ha Hw). exact (H1 a Ha Hw). Qed.
(* A run of the walk: no region of d2_rs is writable, so the run keeps every byte. *)
Lemma d2_keep_run : forall W mf m0 m1 m2 E rs,
d2_keep W mf m0 m1 -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
frame_of E rs (rd W m1) (rd W m2) -> d2_keep W mf m0 m2.
Proof.
intros W mf m0 m1 m2 E rs H Hro HF a Ha Hw. rewrite <- (H a Ha Hw). apply aview_eq_of. apply HF.
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hr1. apply Z.leb_le in Hr1. lia.
Qed.
Lemma d2_vm_keep : forall (W : world SEGS) mf m0 m a n v, d2_keep W mf m0 m ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= mf - 2 * ESTACK \/ mf <= a) ->
val_mem SEGS (rd W m0) a n v -> val_mem SEGS (rd W m) a n v.
Proof.
intros W mf m0 m a n v H Ha Hn Hw Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m0 m a n v); [|exact Hv].
intros k Hk. apply H; lia.
Qed.
Lemma d2_ba_keep : forall (W : world SEGS) mf m0 m a l, d2_keep W mf m0 m ->
0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (a + Z.of_nat (length l) <= mf - 2 * ESTACK \/ mf <= a) ->
bytes_at8 W m0 a l -> bytes_at8 W m a l.
Proof.
intros W mf m0 m a l H Ha Hn Hw Hb. unfold bytes_at8 in *. apply (garr8_frame SEGS (rd W m0) (rd W m) a _ Hb).
intros x Hx. rewrite length_map in Hx. apply mbyte_of_aview. apply H; lia.
Qed.
(* The shadow of a frame or heap address lies below the allocation ceiling. *)
Lemma d2_sh_low : forall a k, 0 <= a <= 2 ^ 47 -> 0 <= k <= 64 -> SHADOW_OFF + a / 8 + k <= alloc_ceiling.
Proof.
intros a k Ha Hk. pose proof asan_consts as (C1 & _). unfold SHADOW_OFF.
assert (a / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma d2_bs_keep : forall (W : world SEGS) mf m0 m a n, d2_keep W mf m0 m ->
0 <= a <= 2 ^ 47 -> 0 <= n <= 64 -> alloc_ceiling <= mf - 2 * ESTACK ->
sh_blk W m0 a n -> sh_blk W m a n.
Proof.
intros W mf m0 m a n H Ha Hn Hc Hb. unfold sh_blk in *. apply (block_shadow_agree (aview SEGS (w_H W) m0) (aview SEGS (w_H W) m) SHADOW_OFF a n); [|exact Hb].
intros i Hi. unfold shadow_of_addr. assert ((n + 7) / 8 <= 64) by (apply Z.div_le_upper_bound; lia).
pose proof (d2_sh_low a (i + 1) Ha ltac:(lia)). assert (0 <= a / 8) by (apply Z.div_pos; lia).
pose proof asan_consts as (C1 & _). apply H; unfold SHADOW_OFF in *; lia.
Qed.
Lemma d2_sz_keep : forall (W : world SEGS) mf m0 m a n, d2_keep W mf m0 m ->
0 <= a <= 2 ^ 47 -> 0 <= n <= 64 -> alloc_ceiling <= mf - 2 * ESTACK ->
sh_zero W m0 a n -> sh_zero W m a n.
Proof.
intros W mf m0 m a n H Ha Hn Hc Hb i Hi. rewrite <- (Hb i Hi). unfold shadow_of_addr.
assert (n / 8 <= 64) by (apply Z.div_le_upper_bound; lia).
pose proof (d2_sh_low a (i + 1) Ha ltac:(lia)). assert (0 <= a / 8) by (apply Z.div_pos; lia).
pose proof asan_consts as (C1 & _). apply H; unfold SHADOW_OFF in *; lia.
Qed.
(* The bytes of a byte list in memory, as the view reads them. *)
Lemma d2_aview_at : forall (W : world SEGS) m a l j, bytes_at8 W m a l -> (j < length l)%nat ->
aview SEGS (w_H W) m (a + Z.of_nat j) = Some (bv_unsigned (nth j l (Z_to_bv 8 0))).
Proof.
intros W m a l j H Hj. unfold aview. unfold bytes_at8 in H.
rewrite (garr8_mbyte SEGS _ a _ j H) by (rewrite length_map; exact Hj). cbn [option_map]. f_equal.
pose proof (proj2 (H j ltac:(rewrite length_map; exact Hj))) as R.
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 8) with 256; exact R).
exact (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) j).
Qed.

Lemma d2_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [p ->]. destruct Hb as [q ->]. exists (2 * p - q). ring.
Qed.

Lemma d2_hwb_len : forall inp i, (length (SlotModel.rec_hwb inp i) <= 8)%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : forall h, SlotModel.rec_hw inp i = Some h -> (length h <= 8)%nat).
{ induction i as [|i IH]; intros h Hh; cbn [SlotModel.rec_hw] in Hh; [discriminate|].
revert Hh. destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k inp i)); intros Hh.
- injection Hh as <-. rewrite length_firstn. lia.
- exact (IH h Hh). }
destruct (SlotModel.rec_hw inp i) as [h|] eqn:E; [exact (H h eq_refl) | rewrite repeat_length; lia].
Qed.

(* The symbolic state rebuilt at a later slot of the segment, from the D1 state's facts and what was kept. *)
Lemma d2_entry_k : forall (g : ectx) pos mf i (W : world SEGS) regs mem0 mem pc,
getr regs 9 = w64 mf -> 0 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling -> alloc_ceiling <= mf - 2 * ESTACK ->
mf + 192 <= 2 ^ 64 -> d2_keep W mf mem0 mem ->
mf_fixed g pos mf W mem0 -> mf_again g pos mf W mem0 -> mf_id g pos mf W mem0 ->
val_mem SEGS (rd W mem0) (mf + 168) 8 SHADOW_OFF ->
bytes_at8 W mem0 (SFa g pos + V_again) (m_id g (S i)) ->
bytes_at8 W mem0 (SFa g pos + V_id) (m_id g (S i)) ->
st_ok_pi SEGS VAL (E_D2 regs (SFa g pos) (m_id g (S i))) (ss_D2 pc)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros g pos mf i W regs mem0 mem pc H9 G1 G2 G4 Hm HK Hfix Hag Hid H168 Bag Bid.
pose proof asan_consts as (C1 & _). unfold ESTACK in G4.
assert (L1 : length (m_id g (S i)) = 38%nat) by (unfold m_id; apply SlotModel.rec_id_length).
assert (VH : forall c v, 0 <= c -> c + 8 <= 192 -> val_mem SEGS (rd W mem0) (mf + c) 8 v -> val_mem SEGS (rd W mem) (mf + c) 8 v).
{ intros c v Hc Hc8. apply (d2_vm_keep W mf mem0 mem _ 8 v HK); unfold ESTACK; lia. }
destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
unfold mf_again, mf_id in *.
apply (d2_entry g pos mf i W regs mem pc H9); [lia | lia | lia | lia | | | | | |].
- unfold mf_fixed. repeat split; apply VH; first [lia | assumption].
- apply VH; [lia | lia | exact Hag].
- apply VH; [lia | lia | exact Hid].
- apply VH; [lia | lia | exact H168].
- apply (d2_ba_keep W mf mem0 mem _ _ HK); [unfold V_again; lia | unfold V_again; lia | unfold ESTACK, V_again; lia | exact Bag].
- apply (d2_ba_keep W mf mem0 mem _ _ HK); [unfold V_id; lia | unfold V_id; lia | unfold ESTACK, V_id; lia | exact Bid].
Qed.
Lemma d2_zext_atom : forall E n (w : N) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ Z.of_N w -> Z.of_N w <= 64 ->
sv_denot E (SExt false w (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n w v Hn Hv Hw.
assert (H64 : 2 ^ Z.of_N w <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
assert (H : U E (SExt false w (SOff n 0)) = v).
{ rewrite U_zext, (U_atom E n v Hn) by lia. apply Z.mod_small. exact Hv. }
unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma d2_pres : forall (regsT regs3 : bvmap 5 word) (r : bv 5) v,
aregs_preserved regsT regs3 -> acallee_saved (bv_unsigned r) -> getr regsT r = v -> getr regs3 r = v.
Proof.
intros regsT regs3 r v HP Hcs Hv. pose proof (HP (bv_unsigned r) Hcs) as E. rewrite !Z_to_bv_bv_unsigned in E.
rewrite E. exact Hv.
Qed.
Lemma d2_addr : forall inp i, SlotModel.rec_r inp i = 1 ->
SlotModel.rec_addr inp i = RcIdentModel.ADDR_FIRMWARE \/ SlotModel.rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION \/
SlotModel.rec_addr inp i = RcIdentModel.ADDR_MODEL_NAME.
Proof.
intros inp i. unfold SlotModel.rec_r, RcIdentModel.ING.
destruct (Z.eqb_spec (SlotModel.rec_addr inp i) RcIdentModel.ADDR_FIRMWARE) as [E|_]; [intros _; left; exact E|].
destruct (Z.eqb_spec (SlotModel.rec_addr inp i) RcIdentModel.ADDR_MODEL_NAME) as [E|_]; [intros _; right; right; exact E|].
destruct (Z.eqb_spec (SlotModel.rec_addr inp i) RcIdentModel.ADDR_REAC_VERSION) as [E|_]; [intros _; right; left; exact E|].
cbn [fst]. intros H. discriminate H.
Qed.

Lemma d2_zext : forall E n (w : N) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ Z.of_N w -> Z.of_N w <= 64 ->
zext 64 (bv_extract 0 w (ew E n)) = Z_to_bv 64 v.
Proof.
intros E n w v Hn Hv Hw. pose proof (d2_zext_atom E n w v Hn Hv Hw) as X. cbn [sv_denot] in X.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X. exact X.
Qed.
Lemma d2_br_ne : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 -> v <> z ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = true -> False.
Proof.
intros E n v z Hn Hv Hz Hne Hc. rewrite branch_eq_U, (U_atom E n v Hn Hv), (U_lit E z Hz) in Hc.
apply Z.eqb_eq in Hc. exact (Hne Hc).
Qed.
Lemma d2_br_eq : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit v)) = false -> False.
Proof.
intros E n v Hn Hv Hc. rewrite branch_eq_U, (U_atom E n v Hn Hv), (U_lit E v Hv), Z.eqb_refl in Hc. discriminate Hc.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* The hypotheses of the contract's Section (LLVMFuzzerTestOneInput.v) this segment uses, as stated there. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]).

(* Where things lie: the entry's frame below the allocation ceiling, the calls' window [mf - 2 * ESTACK, mf)
   above it (the journal's stack facts and HSTK). *)
Lemma d2_geo : forall (g : ectx) pos mf ly2 S2 W2 mem2 md2 k,
AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf ->
frame_addr ly2 4 pos = SFa g pos /\ 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\
in_app (SFa g pos) 1024 /\ alloc_ceiling <= mf - 2 * ESTACK /\ e_sp0 g mod 16 = 0 /\ e_sp0 g <= 2 ^ 47 /\
2 * ESTACK + 336 <= LLVMF_STK.
Proof.
intros g pos mf ly2 S2 W2 mem2 md2 k HJ Hfrs Hmf.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (EF : frame_addr ly2 4 pos = SFa g pos).
{ unfold SFa, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (F1 & F2 & F3).
rewrite EF in F1, F2, F3. change (fs_frame_bytes 4) with 1024 in F2, F3.
pose proof HSTK as HS. unfold STK_LLVMF, ASTACK in HS. unfold ESTACK.
split; [exact EF|]. split; [lia|]. split; [lia|]. split; [exact F3|]. split; [lia|]. split; [exact Hal16|]. split; lia.
Qed.

(* The bcmp wrapper call at sp = mf on `again`+off and `id`+off, n bytes (0x80de8: off 3, n 17; 0x80e60: off 28,
   n 8). Both ranges hold the same bytes (m_id g (S i)), so the wrapper returns 0. *)
Lemma d2_call : forall (g : ectx) pos mf i ly2 S2 (W2 : world SEGS) mem2 memT mdT (regsT : bvmap 5 word) (off n retk : Z),
AJ g pos ly2 S2 W2 memT mdT (4 * Z.of_nat i + 3) ->
frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
d2_keep W2 mf mem2 memT ->
bytes_at8 W2 mem2 (SFa g pos + V_again) (m_id g (S i)) -> bytes_at8 W2 mem2 (SFa g pos + V_id) (m_id g (S i)) ->
sh_blk W2 mem2 (SFa g pos + V_again) N_again -> sh_blk W2 mem2 (SFa g pos + V_id) N_id ->
0 <= off -> 0 < n -> off + n <= 38 ->
getr regsT 10 = w64 (SFa g pos + V_again + off) -> getr regsT 11 = w64 (SFa g pos + V_id + off) ->
getr regsT 12 = w64 n -> getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
getr regsT 2 = w64 mf -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
(fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3 /\
AJ g pos ly2 S2 W2 mem3 md3 (4 * Z.of_nat i + 3) /\
aregs_preserved regsT regs3 /\ getr regs3 10 = w64 0 /\ d2_keep W2 mf mem2 mem3 /\ d2_keep W2 mf memT mem3 /\
(forall a, apresent (w_H W2) memT a -> apresent (w_H W2) mem3 a)).
Proof.
intros g pos mf i ly2 S2 W2 mem2 memT mdT regsT off n retk HJ Hfrs Hmf Hmf32 HK Bag Bid Sag Sid Ho Hn Hon
R10 R11 R12 R1 Hrk Hrk2 R2 R3 R4.
destruct (d2_geo g pos mf ly2 S2 W2 memT mdT _ HJ Hfrs (proj1 Hmf)) as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof (proj1 HJ) as HAR. pose proof asan_consts as (C1 & _).
assert (Hin : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hl : length (m_id g (S i)) = 38%nat) by (unfold m_id; apply SlotModel.rec_id_length).
pose proof (d2_bs_keep W2 mf mem2 memT (SFa g pos + V_again) N_again HK ltac:(unfold V_again; lia)
ltac:(unfold N_again; lia) G4 Sag) as SagT.
pose proof (d2_bs_keep W2 mf mem2 memT (SFa g pos + V_id) N_id HK ltac:(unfold V_id; lia)
ltac:(unfold N_id; lia) G4 Sid) as SidT.
set (sf := SFa g pos) in *. set (l := m_id g (S i)) in *.
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hsp : spZ regsT = e_sp0 g + (mf - e_sp0 g)) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (KLO : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W2) memT a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha; apply HK; lia).
assert (Vx : forall j, 0 <= j < n -> aview SEGS (w_H W2) memT (sf + V_again + off + j) =
Some (bv_unsigned (nth (Z.to_nat (off + j)) l (Z_to_bv 8 0)))).
{ intros j Hj. rewrite KLO by (unfold V_again; lia).
replace (sf + V_again + off + j) with (sf + V_again + Z.of_nat (Z.to_nat (off + j))) by lia.
apply d2_aview_at; [exact Bag | lia]. }
assert (Vy : forall j, 0 <= j < n -> aview SEGS (w_H W2) memT (sf + V_id + off + j) =
Some (bv_unsigned (nth (Z.to_nat (off + j)) l (Z_to_bv 8 0)))).
{ intros j Hj. rewrite KLO by (unfold V_id; lia).
replace (sf + V_id + off + j) with (sf + V_id + Z.of_nat (Z.to_nat (off + j))) by lia.
apply d2_aview_at; [exact Bid | lia]. }
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IB___interceptor_trampoline_bcmp) ABCMP W2 regsT memT
LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 mdT (4 * Z.of_nat i + 3)
(sf + V_again + off) (sf + V_id + off) n (mf - e_sp0 g) (Z_to_bv 64 (BASE + retk)) HJ R10 R11 R12).
- lia.
- unfold V_again; lia.
- unfold V_again; lia.
- unfold V_id; lia.
- unfold V_id; lia.
- exact Hsp.
- apply d2_mod16; assumption.
- lia.
- lia.
- exact R3.
- exact R4.
- exact R1.
- apply ret_ok_codeptr_v; [lia | exact Hrk2].
- intros a Ha. split; [replace a with (sf + V_again + off + (a - (sf + V_again + off))) by lia; rewrite Vx by lia; discriminate|].
rewrite Hsp. unfold V_again in *. lia.
- intros a Ha. split; [replace a with (sf + V_id + off + (a - (sf + V_id + off))) by lia; rewrite Vy by lia; discriminate|].
rewrite Hsp. unfold V_id in *. lia.
- intros a Ha. unfold V_again in *. lia.
- intros a Ha. unfold V_id in *. lia.
- apply (amem_range_sub_app sf 1024 _ n G3 G2); unfold V_again; lia.
- apply (amem_range_sub_app sf 1024 _ n G3 G2); unfold V_id; lia.
- apply (block_shadow_range _ SHADOW_OFF (sf + V_again) N_again _ _ SagT); unfold N_again; lia.
- intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 memT mdT 4 pos _ n HAR Hin);
[rewrite EF; unfold V_again; lia | rewrite EF; change (fs_frame_bytes 4) with 1024; unfold V_again; lia | exact Hn].
- apply (block_shadow_range _ SHADOW_OFF (sf + V_id) N_id _ _ SidT); unfold N_id; lia.
- intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 memT mdT 4 pos _ n HAR Hin);
[rewrite EF; unfold V_id; lia | rewrite EF; change (fs_frame_bytes 4) with 1024; unfold V_id; lia | exact Hn]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr & Hpres).
assert (HK3 : d2_keep W2 mf memT mem3) by (intros a Ha Hw; apply Hfr; [exact Ha | lia]).
split; [reflexivity|]. exists regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
split; [rewrite Hv; apply Hcmp; intros j Hj; rewrite Vx, Vy by exact Hj; reflexivity|].
split; [exact (d2_keep_trans W2 mf mem2 memT mem3 HK HK3)|]. split; [exact HK3 | exact Hpres].
Qed.

(* What every exit of the segment carries, at the exit's registers and memory: the entry's common part, the
   record body, `hw`, and (for the ignored-record exit) the shadow of `id` and `before` and the bytes of `before`.
   The calls changed only their window and the walk changed no register these name. *)
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
Ltac d2_lia := unfold V_before, V_again, V_id, V_hw, N_id, N_before, N_again, N_hw, m_hwb in *; lia.
Lemma d2_core : forall (g : ectx) pos mf i pl ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs3 mem3 md3,
AJ g pos ly2 S2 W2 mem3 md3 (4 * Z.of_nat i + 3) -> frames S2 = [(4, pos)] ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
P_body B g pos mf i pl ly2 S2 W2 regs2 mem2 -> hw_live g pos mf i W2 mem2 ->
sh_blk W2 mem2 (SFa g pos + V_before) N_before ->
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) ->
d2_keep W2 mf mem2 mem3 ->
getr regs3 2 = getr regs2 2 -> getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
getr regs3 8 = getr regs2 8 -> getr regs3 9 = getr regs2 9 -> getr regs3 22 = getr regs2 22 ->
getr regs3 27 = getr regs2 27 ->
ECOMMON g pos mf ly2 S2 W2 regs3 mem3 md3 /\ P_body B g pos mf i pl ly2 S2 W2 regs3 mem3 /\
hw_live g pos mf i W2 mem3 /\
sh_blk W2 mem3 (SFa g pos + V_before) N_before /\ bytes_at8 W2 mem3 (SFa g pos + V_before) (m_id g i).
Proof.
intros g pos mf i pl ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HJ3 Hfrs HEC HPB HHW Sbef Bbef HK
E2 E3 E4 E8 E9 E22 E27.
destruct HEC as (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & V16 & V64 & V192 & V168 & Vra & Vs0 & Vs1 & Vs2 & Vs3 & Vs4
& Vs5 & Vs6 & Vs7 & Vs8 & Vs9 & Vs10 & Vs11 & Vflag & Hpre & Hfds & Hfs & Hinp).
destruct HPB as (Hlt & Hhb & Hpl & Hida & V96 & Hfix & Hbef & Hag & Hid & V112 & V120 & V128 & R22 & R27 & Hcur).
destruct (d2_geo g pos mf ly2 S2 W2 mem3 md3 _ HJ3 Hfrs (proj1 Hmf)) as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof asan_consts as (C1 & _). pose proof (proj1 HJ3) as HAR3. unfold ESTACK in G4, G7.
assert (VH : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v Ha Hn. apply (d2_vm_keep W2 mf mem2 mem3 a n v HK); unfold ESTACK; lia. }
assert (VL : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v Ha Hn. apply (d2_vm_keep W2 mf mem2 mem3 a n v HK); unfold ESTACK; lia. }
assert (BL : forall a l, 0 <= a -> a + Z.of_nat (length l) <= alloc_ceiling ->
bytes_at8 W2 mem2 a l -> bytes_at8 W2 mem3 a l).
{ intros a l Ha Hn. apply (d2_ba_keep W2 mf mem2 mem3 a l HK); unfold ESTACK; lia. }
assert (SB : forall a n, 0 <= a <= 2 ^ 47 -> 0 <= n <= 64 -> sh_blk W2 mem2 a n -> sh_blk W2 mem3 a n)
by (intros a n Ha Hn; exact (d2_bs_keep W2 mf mem2 mem3 a n HK Ha Hn ltac:(unfold ESTACK; lia))).
assert (SZ : forall a n, 0 <= a <= 2 ^ 47 -> 0 <= n <= 64 -> sh_zero W2 mem2 a n -> sh_zero W2 mem3 a n)
by (intros a n Ha Hn; exact (d2_sz_keep W2 mf mem2 mem3 a n HK Ha Hn ltac:(unfold ESTACK; lia))).
assert (L0 : length (m_id g i) = 38%nat) by (unfold m_id; apply SlotModel.rec_id_length).
assert (L1 : length (m_id g (S i)) = 38%nat) by (unfold m_id; apply SlotModel.rec_id_length).
pose proof (d2_hwb_len (e_pl g) i) as L2.
pose proof (SlotModel.rec_pl_length (e_pl g) i) as L3. pose proof (SlotModel.rec_k_range (e_pl g) i) as L4.
assert (HplB : In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2)).
{ destruct Hhb as [Hp _]. apply (Permutation_in _ (Permutation_sym Hp)). left. reflexivity. }
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem3 md3 pl _ HAR3 HplB) as (_ & Hpl0 & Hpl1 & _).
pose proof (req_size_pos (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as [_ Hrk].
assert (Hinp3 : bytes_at8 W2 mem3 (e_p g) (e_pl g)).
{ pose proof Hpre as Hpre'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & Hblk & Hlen & _).
destruct Hblk as [(Hn0 & _) | (_ & Hin)].
- assert (Hnil : e_pl g = []) by (destruct (e_pl g); [reflexivity | cbn [length] in Hlen; lia]).
unfold bytes_at8. rewrite Hnil. cbn [map]. apply garr8_nil.
- assert (Hin2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hhb as [Hp _]. apply (Permutation_in _ (Permutation_sym Hp)). right. exact Hin. }
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem3 md3 _ _ HAR3 Hin2) as (_ & Hp0 & Hp1 & _ & _ & _ & Hpn).
pose proof (req_size_pos (e_n g) ltac:(lia)) as [_ Hrn].
apply BL; [lia | lia | exact Hinp]. }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Hfd3 Hfs3].
destruct HHW as ((Bhw & Shw & BShw) & Vhw & V24).
destruct Hida as (Bida & Sida & BSida).
destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
unfold mf_before in Hbef. unfold mf_again in Hag. unfold mf_id in Hid.
split; [|split; [|split; [|split]]].
- unfold ecommon.
split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|]. split; [rewrite E8; exact R8|].
split; [exact Hmf|]. split; [exact Hmf32|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split; [apply VH; [lia | lia | exact V16]|]. split; [apply VH; [lia | lia | exact V64]|].
split; [apply VH; [lia | lia | exact V192]|]. split; [apply VH; [lia | lia | exact V168]|].
split; [apply VH; [lia | lia | exact Vra]|]. split; [apply VH; [lia | lia | exact Vs0]|].
split; [apply VH; [lia | lia | exact Vs1]|]. split; [apply VH; [lia | lia | exact Vs2]|].
split; [apply VH; [lia | lia | exact Vs3]|]. split; [apply VH; [lia | lia | exact Vs4]|].
split; [apply VH; [lia | lia | exact Vs5]|]. split; [apply VH; [lia | lia | exact Vs6]|].
split; [apply VH; [lia | lia | exact Vs7]|]. split; [apply VH; [lia | lia | exact Vs8]|].
split; [apply VH; [lia | lia | exact Vs9]|]. split; [apply VH; [lia | lia | exact Vs10]|].
split; [apply VH; [lia | lia | exact Vs11]|]. split; [apply VL; [lia | lia | exact Vflag]|].
split; [exact Hpre|]. split; [intros fd; rewrite Hfd3; reflexivity|]. split; [exact Hfs3 | exact Hinp3].
- unfold P_body.
split; [exact Hlt|]. split; [exact Hhb|]. split; [apply BL; [lia | lia | exact Hpl]|].
split; [split; [apply BL; [d2_lia | d2_lia | exact Bida] |
split; [apply SZ; [d2_lia | d2_lia | exact Sida] | apply SB; [d2_lia | d2_lia | exact BSida]]]|].
split; [apply VH; [lia | lia | exact V96]|].
split; [unfold mf_fixed; repeat split; apply VH; first [lia | assumption]|].
split; [apply VH; [lia | lia | exact Hbef]|]. split; [apply VH; [lia | lia | exact Hag]|].
split; [apply VH; [lia | lia | exact Hid]|].
split; [apply VH; [lia | lia | exact V112]|]. split; [apply VH; [lia | lia | exact V120]|].
split; [apply VH; [lia | lia | exact V128]|].
split; [rewrite E22; exact R22|]. split; [rewrite E27; exact R27 | exact Hcur].
- split; [split; [apply BL; [d2_lia | d2_lia | exact Bhw] |
split; [apply SZ; [d2_lia | d2_lia | exact Shw] | apply SB; [d2_lia | d2_lia | exact BShw]]]|].
split; [apply VL; [d2_lia | d2_lia | exact Vhw] | apply VH; [lia | lia | exact V24]].
- apply SB; [d2_lia | d2_lia | exact Sbef].
- apply BL; [d2_lia | d2_lia | exact Bbef].
Qed.

(* ---- the walk -------------------------------------------------------------------------------------------- *)
#[local] Notation D1END := (inv_D1_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
Ltac d2_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac d2_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
let z := eval vm_compute in (bv_unsigned x) in change (acallee_saved z) end; unfold acallee_saved; lia.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* inv_D1_end's P, as one name. *)
Definition d2_P1 (g : ectx) (pos mf : Z) (i : nat) (pl : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
P_body B g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_live g pos mf i W2 mem2 /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before /\
sh_blk W2 mem2 (SFa g pos + V_again) N_again /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
bytes_at8 W2 mem2 (SFa g pos + V_again) (m_id g (S i)) /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 20 = w64 (SlotModel.rec_r (e_pl g) i) /\
getr regs2 26 = w64 (SlotModel.rec_r (e_pl g) i).
(* A state of the segment after one of its calls: the D1 state (regs2, mem2, md2) it started from, the current
   state (regs3, mem3, md3) on the same journal, every byte outside the calls' window kept, the registers the
   exits name unchanged, and RF of the current registers. *)
Definition d2_mid (g : ectx) (pos mf : Z) (i : nat) (pl : Z) (pc : Z) (RF : bvmap 5 word -> Prop)
: world SEGS -> config -> Prop :=
fun W3 c3 => exists ly2 S2 regs2 mem2 md2 regs3 mem3 md3,
c3 = cfg_at SEGS pc regs3 mem3 md3 /\
AJ g pos ly2 S2 W3 mem2 md2 (4 * Z.of_nat i + 3) /\ frames S2 = [(4, pos)] /\
0 <= 4 * Z.of_nat i + 3 <= EV_LLVMF /\ mo_le MT (e_S g) S2 ((4 * Z.of_nat i + 3) * MEV MT) /\
mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat i + 3)) * MEV MT) /\
ECOMMON g pos mf ly2 S2 W3 regs2 mem2 md2 /\ d2_P1 g pos mf i pl ly2 S2 W3 regs2 mem2 /\
AJ g pos ly2 S2 W3 mem3 md3 (4 * Z.of_nat i + 3) /\ d2_keep W3 mf mem2 mem3 /\
getr regs3 2 = getr regs2 2 /\ getr regs3 3 = getr regs2 3 /\ getr regs3 4 = getr regs2 4 /\
getr regs3 8 = getr regs2 8 /\ getr regs3 9 = getr regs2 9 /\ getr regs3 18 = getr regs2 18 /\
getr regs3 20 = getr regs2 20 /\ getr regs3 22 = getr regs2 22 /\ getr regs3 27 = getr regs2 27 /\
RF regs3.
(* The `again` fields loaded before the first call (s10 at 0x80db0, s7 at 0x80dc8) and before the second
   (s3 at 0x80df8, s8 at 0x80e10, s9 at 0x80e28, s5 at 0x80e40); a0 is the call's result. *)
Definition d2_RF1 (g : ectx) (i : nat) (r : bvmap 5 word) : Prop :=
getr r 10 = w64 0 /\ getr r 26 = w64 (d2_h (m_id g (S i)) 0) /\ getr r 23 = w64 (d2_b (m_id g (S i)) 2).
Definition d2_RF2 (g : ectx) (i : nat) (r : bvmap 5 word) : Prop :=
d2_RF1 g i r /\ getr r 19 = w64 (d2_b (m_id g (S i)) 20) /\ getr r 24 = w64 (d2_h (m_id g (S i)) 22) /\
getr r 25 = w64 (d2_h (m_id g (S i)) 24) /\ getr r 21 = w64 (d2_h (m_id g (S i)) 26).

(* An exit of the switch: the cut at pc from the D1 state, the exit's state and what the exit's case adds. *)
Lemma d2_exit : forall (g : ectx) pos mf i pl ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs4 mem4 md4 (pc : Z)
(P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
frames S2 = [(4, pos)] ->
0 <= 4 * Z.of_nat i + 3 <= EV_LLVMF -> mo_le MT (e_S g) S2 ((4 * Z.of_nat i + 3) * MEV MT) ->
mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat i + 3)) * MEV MT) ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> d2_P1 g pos mf i pl ly2 S2 W2 regs2 mem2 ->
AJ g pos ly2 S2 W2 mem4 md4 (4 * Z.of_nat i + 3) -> d2_keep W2 mf mem2 mem4 ->
getr regs4 2 = getr regs2 2 -> getr regs4 3 = getr regs2 3 -> getr regs4 4 = getr regs2 4 ->
getr regs4 8 = getr regs2 8 -> getr regs4 9 = getr regs2 9 -> getr regs4 22 = getr regs2 22 ->
getr regs4 27 = getr regs2 27 ->
(P_body B g pos mf i pl ly2 S2 W2 regs4 mem4 -> hw_live g pos mf i W2 mem4 ->
 sh_blk W2 mem4 (SFa g pos + V_before) N_before -> bytes_at8 W2 mem4 (SFa g pos + V_before) (m_id g i) ->
 P ly2 S2 W2 regs4 mem4 md4) ->
ACUT g pos mf (4 * Z.of_nat i + 3) pc P W2 (cfg_at SEGS pc regs4 mem4 md4).
Proof.
intros g pos mf i pl ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 pc P Hfrs Hk Hmle Hmok HEC HP HJ4 HK
E2 E3 E4 E8 E9 E22 E27 HPP.
destruct HP as (HPB & HHW & Sbef & _ & Bbef & _).
destruct (d2_core g pos mf i pl ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HJ4 Hfrs HEC HPB HHW Sbef Bbef HK
E2 E3 E4 E8 E9 E22 E27) as (HEC4 & HPB4 & HHW4 & Sbef4 & Bbef4).
exists ly2, S2, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hmle|].
split; [exact Hmok|]. split; [exact HEC4|]. exact (HPP HPB4 HHW4 Sbef4 Bbef4).
Qed.

(* Part 1, +0x630 .. the first bcmp call (0x80de8) and its return to 0x80dec: the result compare (0x80da4, r2 = r),
   the fields +0 and +2 of `again` against `id`, and the call on model_name (17 bytes at +3). *)
Lemma d2_p1 : forall g pos mf i pl W2 c2, D1END g pos mf i pl W2 c2 ->
SRr SEGS W2 c2 (d2_mid g pos mf i pl (BASE + 0x678) (d2_RF1 g i)).
Proof.
intros g pos mf i pl W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & Hmle & Hmok & HEC & HP).
change (d2_P1 g pos mf i pl ly2 S2 W2 regs2 mem2) in HP.
pose proof HJ as HJ0.
pose proof HEC as (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & _ & _ & _ & V168 & _).
pose proof HP as (HPB & _ & _ & Sag & _ & Bag & _ & R20 & R26).
pose proof HPB as (_ & _ & _ & Hida & _ & Hfix & _ & Hag & Hid & _).
destruct (d2_geo g pos mf ly2 S2 W2 mem2 md2 _ HJ Hfrs (proj1 Hmf)) as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof asan_consts as (C1 & _). unfold ESTACK in G4, G7.
pose proof (d2_entry g pos mf i W2 regs2 mem2 0x630 R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
Hfix Hag Hid V168 Bag (proj1 Hida)) as HS.
remember (E_D2 regs2 (SFa g pos) (m_id g (S i))) as E eqn:HE.
assert (EX : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs2 (d2_extra (SFa g pos) (m_id g (S i)))) n)
by (intros n Hn; subst E; unfold E_D2; apply Eimg_low; unfold A_TEXT; lia).
assert (HAE : env_agree 32 (Ereg regs2 (d2_extra (SFa g pos) (m_id g (S i)))) E) by (split; [exact EX | subst E; reflexivity]).
assert (E2 : ew E 2 = getr regs2 2) by (rewrite EX by lia; exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs2 3) by (rewrite EX by lia; exact (ew_Ereg_nat regs2 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs2 4) by (rewrite EX by lia; exact (ew_Ereg_nat regs2 _ 4 4%bv eq_refl)).
assert (E20 : ew E 20 = getr regs2 20) by (rewrite EX by lia; exact (ew_Ereg_nat regs2 _ 20 20%bv eq_refl)).
assert (E26 : ew E 26 = getr regs2 26) by (rewrite EX by lia; exact (ew_Ereg_nat regs2 _ 26 26%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos)) by (subst E; exact (d2_ew_extra regs2 (SFa g pos) (m_id g (S i)) 0 ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (d2_h (m_id g (S i)) 0)) by (subst E; exact (d2_ew_extra regs2 (SFa g pos) (m_id g (S i)) 1 ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (d2_b (m_id g (S i)) 2)) by (subst E; exact (d2_ew_extra regs2 (SFa g pos) (m_id g (S i)) 2 ltac:(lia))).
assert (SHOK : sh_ok SEGS Bx_D2 [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold E_D2; apply Eimg_env).
clear HE.
assert (HK0 : d2_keep W2 mf mem2 mem2) by apply d2_keep_refl.
unfold cfg_at. change (w64 (BASE + 0x630)) with (Z_to_bv 64 (BASE + 0x630)).
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
2:{ exfalso. rewrite branch_eq_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
rewrite E26, E20, R26, R20, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|].
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
assert (HK1 : d2_keep W2 mf mem2 m2) by exact (d2_keep_run W2 mf mem2 m1 m2 _ rs HK0 ltac:(vm_compute; reflexivity) HFr) end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
prreg HS (23%bv : bv 5) R23x; prreg HS (26%bv : bv 5) R26x;
pose proof (regs_kept_of_st_ok SEGS E _ _ regs2 (d2_extra (SFa g pos) (m_id g (S i))) [2; 3; 4; 8; 9; 18; 20; 22; 27]%bv HS HAE
ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR;
pmkst HS end.
eapply SRr_mono.
{ eapply (d2_call g pos mf i ly2 S2 W2 mem2 _ _ _ 3 17 0x678 HJ Hfrs Hmf Hmf32 HK1 Bag (proj1 Hida)
Sag (proj2 (proj2 Hida))).
- lia. - lia. - lia.
- rewrite Ra0, E32, unsigned_lit_small by lia. unfold w64, V_again. f_equal. lia.
- rewrite Ra1, E32, unsigned_lit_small by lia. unfold w64, V_id. f_equal. lia.
- rewrite Ra2. reflexivity.
- rewrite Rra. reflexivity.
- lia.
- reflexivity.
- rewrite Rsp, E2. exact R2.
- rewrite Rgp, E3. exact R3.
- rewrite Rtp, E4. exact R4. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & R10' & HK3 & _ & _).
exists ly2, S2, regs2, mem2, md2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ0|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hmle|].
split; [exact Hmok|]. split; [exact HEC|]. split; [exact HP|]. split; [exact HJ3|]. split; [exact HK3|].
do 9 (split; [apply (d2_pres _ _ _ _ HP3); [d2_cs | apply HKR; d2_in]|]).
split; [exact R10'|]. split.
- apply (d2_pres _ _ _ _ HP3); [d2_cs|]. rewrite R26x.
apply (d2_zext E 33 16 _ E33); [pose proof (d2_h_range (m_id g (S i)) 0); change (2 ^ Z.of_N 16) with 65536; lia | cbn; lia].
- apply (d2_pres _ _ _ _ HP3); [d2_cs|]. rewrite R23x.
apply (d2_zext E 34 8 _ E34); [pose proof (d2_b_range (m_id g (S i)) 2); change (2 ^ Z.of_N 8) with 256; lia | cbn; lia].
Qed.


(* Part 2, the return of the first call (0x80dec) .. the second bcmp call (0x80e60) and its return to 0x80e64: the
   call's result, the fields +20, +22, +24, +26 of `again` against `id`, and the call on reac_version_raw
   (8 bytes at +28). *)
Lemma d2_p2 : forall g pos mf i pl W2 c3, d2_mid g pos mf i pl (BASE + 0x678) (d2_RF1 g i) W2 c3 ->
SRr SEGS W2 c3 (d2_mid g pos mf i pl (BASE + 0x6f0) (d2_RF2 g i)).
Proof.
intros g pos mf i pl W2 c3 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & regs3 & mem3 & md3 & -> & HJ0 & Hfrs & Hk & Hmle & Hmok & HEC & HP &
HJ & HK & E2' & E3' & E4' & E8' & E9' & E18' & E20' & E22' & E27' & RF).
destruct RF as (R10 & R26' & R23').
pose proof HEC as (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & _ & _ & _ & V168 & _).
pose proof HP as (HPB & _ & _ & Sag & _ & Bag & _ & _ & _).
pose proof HPB as (_ & _ & _ & Hida & _ & Hfix & _ & Hag & Hid & _).
destruct (d2_geo g pos mf ly2 S2 W2 mem3 md3 _ HJ Hfrs (proj1 Hmf)) as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof asan_consts as (C1 & _).
assert (R9' : getr regs3 9 = w64 mf) by (rewrite E9'; exact R9).
pose proof (d2_entry_k g pos mf i W2 regs3 mem2 mem3 0x678 R9' ltac:(lia) G2 G4 ltac:(unfold ESTACK in G4; lia)
HK Hfix Hag Hid V168 Bag (proj1 Hida)) as HS.
unfold ESTACK in G4, G7.
remember (E_D2 regs3 (SFa g pos) (m_id g (S i))) as E eqn:HE.
assert (EX : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs3 (d2_extra (SFa g pos) (m_id g (S i)))) n)
by (intros n Hn; subst E; unfold E_D2; apply Eimg_low; unfold A_TEXT; lia).
assert (HAE : env_agree 32 (Ereg regs3 (d2_extra (SFa g pos) (m_id g (S i)))) E) by (split; [exact EX | subst E; reflexivity]).
assert (E2 : ew E 2 = getr regs3 2) by (rewrite EX by lia; exact (ew_Ereg_nat regs3 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs3 3) by (rewrite EX by lia; exact (ew_Ereg_nat regs3 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs3 4) by (rewrite EX by lia; exact (ew_Ereg_nat regs3 _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite EX by lia; rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact R10).
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos)) by (subst E; exact (d2_ew_extra regs3 (SFa g pos) (m_id g (S i)) 0 ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (d2_b (m_id g (S i)) 20)) by (subst E; exact (d2_ew_extra regs3 (SFa g pos) (m_id g (S i)) 3 ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (d2_h (m_id g (S i)) 22)) by (subst E; exact (d2_ew_extra regs3 (SFa g pos) (m_id g (S i)) 4 ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (d2_h (m_id g (S i)) 24)) by (subst E; exact (d2_ew_extra regs3 (SFa g pos) (m_id g (S i)) 5 ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (d2_h (m_id g (S i)) 26)) by (subst E; exact (d2_ew_extra regs3 (SFa g pos) (m_id g (S i)) 6 ltac:(lia))).
assert (SHOK : sh_ok SEGS Bx_D2 [] E (mrestrict (w_H W2) mem3)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold E_D2; apply Eimg_env).
clear HE.
unfold cfg_at. change (w64 (BASE + 0x678)) with (Z_to_bv 64 (BASE + 0x678)).
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
2:{ exfalso. exact (d2_br_eq E 10 0 E10 ltac:(lia) Hc). }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|].
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
assert (HK1 : d2_keep W2 mf mem2 m2) by exact (d2_keep_run W2 mf mem2 m1 m2 _ rs HK ltac:(vm_compute; reflexivity) HFr) end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
prreg HS (19%bv : bv 5) R19x; prreg HS (24%bv : bv 5) R24x; prreg HS (25%bv : bv 5) R25x; prreg HS (21%bv : bv 5) R21x;
pose proof (regs_kept_of_st_ok SEGS E _ _ regs3 (d2_extra (SFa g pos) (m_id g (S i)))
[2; 3; 4; 8; 9; 18; 20; 22; 23; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR;
pmkst HS end.
eapply SRr_mono.
{ eapply (d2_call g pos mf i ly2 S2 W2 mem2 _ _ _ 28 8 0x6f0 HJ Hfrs Hmf Hmf32 HK1 Bag (proj1 Hida)
Sag (proj2 (proj2 Hida))).
- lia. - lia. - lia.
- rewrite Ra0, E32, unsigned_lit_small by lia. unfold w64, V_again. f_equal. lia.
- rewrite Ra1, E32, unsigned_lit_small by lia. unfold w64, V_id. f_equal. lia.
- rewrite Ra2. reflexivity.
- rewrite Rra. reflexivity.
- lia.
- reflexivity.
- rewrite Rsp, E2, E2'. exact R2.
- rewrite Rgp, E3, E3'. exact R3.
- rewrite Rtp, E4, E4'. exact R4. }
cbv beta. intros W3 c3 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & R10' & HK4 & _ & _).
exists ly2, S2, regs2, mem2, md2, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ0|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hmle|].
split; [exact Hmok|]. split; [exact HEC|]. split; [exact HP|]. split; [exact HJ4|]. split; [exact HK4|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E2']|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E3']|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E4']|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E8']|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E9']|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E18']|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E20']|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E22']|].
split; [apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact E27']|].
split; [split; [exact R10'|split]|].
- apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact R26'].
- apply (d2_pres _ _ _ _ HP4); [d2_cs | rewrite HKR by d2_in; exact R23'].
- split; [|split; [|split]].
+ apply (d2_pres _ _ _ _ HP4); [d2_cs|]. rewrite R19x.
apply (d2_zext E 35 8 _ E35); [pose proof (d2_b_range (m_id g (S i)) 20); change (2 ^ Z.of_N 8) with 256; lia | cbn; lia].
+ apply (d2_pres _ _ _ _ HP4); [d2_cs|]. rewrite R24x.
apply (d2_zext E 36 16 _ E36); [pose proof (d2_h_range (m_id g (S i)) 22); change (2 ^ Z.of_N 16) with 65536; lia | cbn; lia].
+ apply (d2_pres _ _ _ _ HP4); [d2_cs|]. rewrite R25x.
apply (d2_zext E 37 16 _ E37); [pose proof (d2_h_range (m_id g (S i)) 24); change (2 ^ Z.of_N 16) with 65536; lia | cbn; lia].
+ apply (d2_pres _ _ _ _ HP4); [d2_cs|]. rewrite R21x.
apply (d2_zext E 38 16 _ E38); [pose proof (d2_h_range (m_id g (S i)) 26); change (2 ^ Z.of_N 16) with 65536; lia | cbn; lia].
Qed.


#[local] Notation INV_V := (inv_caseV B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
#[local] Notation INV_M := (inv_caseM B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
#[local] Notation INV_F := (inv_caseF B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
#[local] Notation INV_I := (inv_ignored B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
Ltac d2_keep_step :=
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HKo : d2_keep ?W ?mf ?m0 ?m1 |- _ =>
let HKn := fresh "HK" in
assert (HKn : d2_keep W mf m0 m2) by exact (d2_keep_run W mf m0 m1 m2 _ rs HKo ltac:(vm_compute; reflexivity) HFr);
clear HKo end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* At an exit: the bytes kept, the registers the last part did not write, a0 and a5, then the exit's state. *)
Ltac d2_exit_pre :=
d2_keep_step;
lazymatch goal with HS : st_ok_pi _ _ ?E _ (restrict _ ?msx), HAE : env_agree 32 (Ereg ?regs3 ?xt) ?E |- _ =>
pose proof (regs_kept_of_st_ok_pi E _ _ regs3 xt [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE
ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR;
let R10x := fresh "R10x" in let R15x := fresh "R15x" in
prreg HS (10%bv : bv 5) R10x; prreg HS (15%bv : bv 5) R15x;
pmkst HS end;
lazymatch goal with HKx : d2_keep _ _ _ _ |- _ => rename HKx into HK end;
apply SRr_ret.
Ltac d2_regeq HKR Ex := rewrite HKR by d2_in; exact Ex.

Lemma d2_p3 : forall g pos mf i pl W2 c3, d2_mid g pos mf i pl (BASE + 0x6f0) (d2_RF2 g i) W2 c3 ->
SRr SEGS W2 c3 (fun W4 c4 => INV_V g pos mf i pl W4 c4 \/ INV_M g pos mf i pl W4 c4 \/
INV_F g pos mf i pl W4 c4 \/ INV_I g pos mf i pl W4 c4).
Proof.
intros g pos mf i pl W2 c3 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & regs3 & mem3 & md3 & -> & HJ0 & Hfrs & Hk & Hmle & Hmok & HEC & HP &
HJ & HK & E2' & E3' & E4' & E8' & E9' & E18' & E20' & E22' & E27' & RF).
destruct RF as ((R10 & R26' & R23') & R19' & R24' & R25' & R21').
pose proof HEC as (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & _ & _ & _ & V168 & _).
pose proof HP as (HPB & _ & _ & Sag & _ & Bag & R18 & R20 & _).
pose proof HPB as (_ & _ & _ & Hida & _ & Hfix & _ & Hag & Hid & _).
destruct (d2_geo g pos mf ly2 S2 W2 mem3 md3 _ HJ Hfrs (proj1 Hmf)) as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof asan_consts as (C1 & _).
assert (R9' : getr regs3 9 = w64 mf) by (rewrite E9'; exact R9).
pose proof (d2_entry_k g pos mf i W2 regs3 mem2 mem3 0x6f0 R9' ltac:(lia) G2 G4 ltac:(unfold ESTACK in G4; lia)
HK Hfix Hag Hid V168 Bag (proj1 Hida)) as HS.
unfold ESTACK in G4, G7.
remember (E_D2 regs3 (SFa g pos) (m_id g (S i))) as E eqn:HE.
assert (EX : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs3 (d2_extra (SFa g pos) (m_id g (S i)))) n)
by (intros n Hn; subst E; unfold E_D2; apply Eimg_low; unfold A_TEXT; lia).
assert (HAE : env_agree 32 (Ereg regs3 (d2_extra (SFa g pos) (m_id g (S i)))) E) by (split; [exact EX | subst E; reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite EX by lia; rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact R10).
assert (E18 : ew E 18 = Z_to_bv 64 (SlotModel.rec_addr (e_pl g) i))
by (rewrite EX by lia; rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl), E18'; exact R18).
assert (E20 : ew E 20 = Z_to_bv 64 (SlotModel.rec_r (e_pl g) i))
by (rewrite EX by lia; rewrite (ew_Ereg_nat regs3 _ 20 20%bv eq_refl), E20'; exact R20).
assert (E39 : ew E 39 = Z_to_bv 64 (d2_b (m_id g (S i)) 36)) by (subst E; exact (d2_ew_extra regs3 (SFa g pos) (m_id g (S i)) 7 ltac:(lia))).
assert (SHOK : sh_ok SEGS Bx_D2 [] E (mrestrict (w_H W2) mem3)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold E_D2; apply Eimg_env).
clear HE.
unfold cfg_at. change (w64 (BASE + 0x6f0)) with (Z_to_bv 64 (BASE + 0x6f0)).
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
2:{ exfalso. exact (d2_br_eq E 10 0 E10 ltac:(lia) Hc). }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|].
d2_keep_step.
pose proof (d2_h_range (m_id g (S i)) 22) as RG22. pose proof (d2_b_range (m_id g (S i)) 36) as RG36.
destruct (SlotModel.rec_r_range (e_pl g) i) as [Hr | Hr]; rewrite Hr in E20.
- (* r = 0: the ignored-record path, 0x80e84 beqz s4 taken *)
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
2:{ exfalso. exact (d2_br_eq E 20 0 E20 ltac:(lia) Hc). }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan_D2 0x7b4; [awr_ok_tac|].
d2_exit_pre.
right; right; right. unfold inv_ignored.
eapply (d2_exit g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ _ _ _ _ Hfrs Hk Hmle Hmok HEC HP HJ HK);
[ d2_regeq HKR E2' | d2_regeq HKR E3' | d2_regeq HKR E4' | d2_regeq HKR E8' | d2_regeq HKR E9' | d2_regeq HKR E22' | d2_regeq HKR E27' |].
intros HPB4 HHW4 Sbef4 Bbef4. split; [exact HPB4|]. split; [exact HHW4|]. split; [exact Hr|].
split; [exact Bbef4|]. split; [exact Sbef4|]. rewrite HKR by d2_in. rewrite E18'. exact R18.
- (* r = 1 *)
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
{ exfalso. exact (d2_br_ne E 20 1 0 E20 ltac:(lia) ltac:(lia) ltac:(lia) Hc). }
clear Hc.
destruct (d2_addr _ _ Hr) as [Ha | [Ha | Ha]]; rewrite Ha in E18.
+ (* the firmware record, address 0: 0x80e8c and 0x80e94 not taken, 0x80e9c beqz s2 taken *)
unfold RcIdentModel.ADDR_FIRMWARE in E18.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|]. d2_keep_step.
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
{ exfalso. exact (d2_br_ne E 18 0 4096 E18 ltac:(lia) ltac:(lia) ltac:(lia) Hc). }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|]. d2_keep_step.
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
{ exfalso. exact (d2_br_ne E 18 0 1536 E18 ltac:(lia) ltac:(lia) ltac:(lia) Hc). }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|]. d2_keep_step.
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
2:{ exfalso. exact (d2_br_eq E 18 0 E18 ltac:(lia) Hc). }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan_D2 0x730; [awr_ok_tac|].
d2_exit_pre.
right; right; left. unfold inv_caseF.
eapply (d2_exit g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ _ _ _ _ Hfrs Hk Hmle Hmok HEC HP HJ HK);
[ d2_regeq HKR E2' | d2_regeq HKR E3' | d2_regeq HKR E4' | d2_regeq HKR E8' | d2_regeq HKR E9' | d2_regeq HKR E22' | d2_regeq HKR E27' |].
intros HPB4 HHW4 _ _. split; [exact HPB4|]. split; [exact HHW4|]. split; [exact Hr|]. split; [exact Ha|].
split; [rewrite R15x; reflexivity|].
split; [rewrite HKR by d2_in; exact R23' | rewrite HKR by d2_in; exact R26'].
+ (* the REAC-version record, address 0x600: 0x80e8c not taken, 0x80e94 taken *)
unfold RcIdentModel.ADDR_REAC_VERSION in E18.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|]. d2_keep_step.
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
{ exfalso. exact (d2_br_ne E 18 1536 4096 E18 ltac:(lia) ltac:(lia) ltac:(lia) Hc). }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|]. d2_keep_step.
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
2:{ exfalso. exact (d2_br_eq E 18 1536 E18 ltac:(lia) Hc). }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan_D2 0x888; [awr_ok_tac|].
d2_exit_pre.
left. unfold inv_caseV.
eapply (d2_exit g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ _ _ _ _ Hfrs Hk Hmle Hmok HEC HP HJ HK);
[ d2_regeq HKR E2' | d2_regeq HKR E3' | d2_regeq HKR E4' | d2_regeq HKR E8' | d2_regeq HKR E9' | d2_regeq HKR E22' | d2_regeq HKR E27' |].
intros HPB4 HHW4 _ _. split; [exact HPB4|]. split; [exact HHW4|]. split; [exact Hr|]. split; [exact Ha|].
split; [rewrite R10x; exact (d2_zext E 39 8 _ E39 ltac:(change (2 ^ Z.of_N 8) with 256; lia) ltac:(cbn; lia))|].
split; [rewrite HKR by d2_in; exact R24'|]. split; [rewrite HKR by d2_in; exact R25' | rewrite HKR by d2_in; exact R21'].
+ (* the model-name record, address 0x1000: 0x80e8c taken *)
unfold RcIdentModel.ADDR_MODEL_NAME in E18.
paj_run_tok RUN HS HJ SHOK Bspan_D2; [awr_ok_tac|]. d2_keep_step.
psrr_branch_tok RUN BR HS SHOK Bspan_D2.
2:{ exfalso. exact (d2_br_eq E 18 4096 E18 ltac:(lia) Hc). }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan_D2 0xb44; [awr_ok_tac|].
d2_exit_pre.
right; left. unfold inv_caseM.
eapply (d2_exit g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ _ _ _ _ Hfrs Hk Hmle Hmok HEC HP HJ HK);
[ d2_regeq HKR E2' | d2_regeq HKR E3' | d2_regeq HKR E4' | d2_regeq HKR E8' | d2_regeq HKR E9' | d2_regeq HKR E22' | d2_regeq HKR E27' |].
intros HPB4 HHW4 _ _. split; [exact HPB4|]. split; [exact HHW4|]. split; [exact Hr|]. split; [exact Ha|].
rewrite HKR by d2_in. exact R19'.
Qed.


(* The segment: part 1, part 2 and part 3 chained. *)
Lemma seg_D2 : seg_D2_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf i pl W2 c2 H.
eapply SRr_bind; [exact (d2_p1 g pos mf i pl W2 c2 H)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (d2_p2 g pos mf i pl W3 c3 H3)|]. intros W4 c4 _ H4.
exact (d2_p3 g pos mf i pl W4 c4 H4).
Qed.
Check (seg_D2 : seg_D2_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).

End c.

End b.
End a.
