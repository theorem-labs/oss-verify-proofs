(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfk.v:174-178
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:103-105, 131-135 [Apache-2.0];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YCcc.v:33-37 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC86.v:38-42 [Apache-2.0 OR MIT]. *)
(* Segment D5 of LLVMFuzzerTestOneInput's ASan+UBSan walk (fuzz_identity.asan-ubsan, BASE + 0x730 .. BASE + 0xe24,
   0x80ea4 .. 0x81598): the firmware case of the record switch, seg_D5 of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v.

   The code (the neutral listing of fuzz_identity.asan-ubsan):
     0x80ea4 .. 0x80eb4   n >= 4 (s6 = rec_k) and the `again` record's has_fw byte (s7) is not zero, else abort;
     0x80eb8 .. 0x80f18   the four digit checks: for j = 0 .. 3, the UBSan pointer checks of pl + j (traps 0x80ec8,
                          0x80edc, 0x80ee4), the shadow check of pl + j (slow block 0x80f1c) and pl[j] <= 9;
     0x81364 .. 0x8140c   three more pointer checks, the shadow checks of pl + 1, pl, pl + 2, pl + 3 (the shadow
                          address of pl + 3 is kept at mf+40, 0x813d4), and the abort unless
                          1000 pl[0] + 100 pl[1] + 10 pl[2] + pl[3] equals the `again` record's firmware value (s10);
     0x81414 .. 0x8143c   `s` (SF+192) is unpoisoned (its shadow byte, shadow(SF)+24, set to 0),
                          reac_identity_fw_str (v, s, 8) at 0x8142c and check_str (L v, s, 8) at 0x8143c;
     0x81440 .. 0x81538   the five byte checks: L v = 5, s[0] = pl[0] + '0', s[1] = '.', s[2..4] = pl[1..3] + '0',
                          with the pointer checks of s and pl and the shadow checks of pl again;
     0x8153c .. 0x81548   `s` is poisoned again (0xf8) and the case jumps to the join 0x81598.
   No allocator call, so the event count stays 4 i + 3; hw is not changed (only the version case writes it).

   The walk is four runs of the listing's engine (IdentBPaLib's paj_run tactics) and two calls:
     run A1  +0x730 .. +0xca0, with the shadow entries of pl[0 .. 4) (the shadow base is a5 = atom 15);
     run A2  +0xca0 .. the call of reac_identity_fw_str, with the shadow byte of `s` as a written region and no
             shadow entry (a run that writes shadow memory must not use shadow entries over it);
     call    reac_identity_fw_str (HFWS, the caller-journal form), into the frame's own variable `s`;
     run B   +0xcbc .. the call of check_str;
     call    check_str (HCHK, through d5_aj_call = YCbq.aj_call without the symbolic state), on the six bytes
             the first call wrote;
     run C   +0xccc .. +0xdc8, with the shadow entries of pl again;
     run D   +0xdc8 .. +0xe24, the store of 0xf8 to the shadow byte of `s`.
   The digit sum is decided by an alias of the start state (1000 pl[0] + 100 pl[1] + 10 pl[2] + pl[3] = atom 26,
   the firmware value), and each byte check by the chunks of the region of `s`, which hold pl[j] + 48 as the
   atom of pl[j] with offset 48.

   inv_caseF carries the two `again` registers the case reads first (x23 = its has_fw byte, x26 = its firmware
   value, loaded at 0x80dc8 / 0x80db0). After the first call a0 = L v = 5 is pinned in the symbolic state
   (st_ok_pi_pin_reg'), so that s10 (= a0, 0x81430) decides the check at 0x81444. The meter crosses
   reac_identity_fw_str with the contract's HMT0 and MTL (mo_le_trans, mo_ok_step); check_str leaves the state. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require check_str reac_identity_fw_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_identity_fw_str_c.
Import ListNotations.
(* reac_box_name_seg_*.v set lia's euclidean-division flag to false for every file that loads reac_box_name
   (through the contract); this file was proved with it on, so it turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model of the firmware case (lib/Prog/RcIdentModel.v, SlotModel.v) ---------------------------- *)
(* The shape of lib/Prog/Seg/Tac_sb2.v's sb2_ing_fw / sb2_rec_fw / sb2_FW_digits, for ADDR_FIRMWARE. *)
Lemma d5_bz_zb : forall x, RcIdentModel.bz (RcIdentModel.zb x) = x mod 256.
Proof. intros x. unfold RcIdentModel.bz, RcIdentModel.zb. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma d5_digits : forall p j, RcIdentModel.all_digits (firstn 4 p) = true -> (j < 4)%nat -> (j < length p)%nat ->
  RcIdentModel.bz (RcIdentModel.nthb p j) <= 9.
Proof.
intros p j H Hj Hl. unfold RcIdentModel.all_digits in H. rewrite forallb_forall in H.
assert (E : RcIdentModel.nthb p j = nth j (firstn 4 p) (RcIdentModel.zb 0))
  by (unfold RcIdentModel.nthb; symmetry; apply SlotModel.nth_first; exact Hj).
rewrite E. apply Z.leb_le. apply H. apply nth_In. rewrite length_firstn. lia.
Qed.

Lemma d5_ing_fw : forall idb p, length idb = RcIdentModel.ID_SIZE ->
  fst (RcIdentModel.ING idb RcIdentModel.ADDR_FIRMWARE p) = 1 ->
  (4 <= length p)%nat /\ RcIdentModel.all_digits (firstn 4 p) = true /\
  RcIdentModel.bz (RcIdentModel.nthb (snd (RcIdentModel.ING idb RcIdentModel.ADDR_FIRMWARE p)) 2) = 1 /\
  RcIdentModel.fw_milli (snd (RcIdentModel.ING idb RcIdentModel.ADDR_FIRMWARE p)) = RcIdentModel.fw_value p.
Proof.
intros idb p Hl Hr.
change (RcIdentModel.ING idb RcIdentModel.ADDR_FIRMWARE p) with (RcIdentModel.ing_firmware idb p) in *.
unfold RcIdentModel.ing_firmware in *.
destruct ((4 <=? length p)%nat && RcIdentModel.all_digits (firstn 4 p)) eqn:E; cbn [fst snd] in *; [|discriminate].
apply andb_true_iff in E as [E1 E2]. apply Nat.leb_le in E1.
assert (D : forall j, (j < 4)%nat -> 0 <= RcIdentModel.bz (RcIdentModel.nthb p j) <= 9).
{ intros j Hj. split; [unfold RcIdentModel.bz; apply bv_unsigned_in_range | apply d5_digits; [exact E2 | exact Hj | lia]]. }
assert (V : 0 <= RcIdentModel.fw_value p <= 9999).
{ unfold RcIdentModel.fw_value. pose proof (D 0%nat ltac:(lia)). pose proof (D 1%nat ltac:(lia)).
  pose proof (D 2%nat ltac:(lia)). pose proof (D 3%nat ltac:(lia)). lia. }
assert (L1 : length (RcIdentModel.upd idb RcIdentModel.OFF_FW (RcIdentModel.le16 (RcIdentModel.fw_value p))) = length idb)
  by (apply RcIdentModel.upd_length; rewrite Hl; cbn; unfold RcIdentModel.OFF_FW, RcIdentModel.ID_SIZE; lia).
split; [exact E1|]. split; [exact E2|]. split.
- unfold RcIdentModel.nthb, RcIdentModel.OFF_HAS_FW.
  rewrite SlotModel.nth_upd_in by (rewrite ?L1, ?Hl; cbn [length]; unfold RcIdentModel.ID_SIZE; lia).
  cbn [Nat.sub nth]. rewrite d5_bz_zb. reflexivity.
- unfold RcIdentModel.fw_milli, RcIdentModel.nthb.
  rewrite (SlotModel.nth_upd_before _ _ RcIdentModel.OFF_HAS_FW 0), (SlotModel.nth_upd_before _ _ RcIdentModel.OFF_HAS_FW 1)
    by (rewrite ?L1, ?Hl; unfold RcIdentModel.OFF_HAS_FW, RcIdentModel.ID_SIZE; lia).
  unfold RcIdentModel.OFF_FW.
  rewrite !SlotModel.nth_upd_in by (rewrite ?Hl; cbn [length RcIdentModel.le16]; unfold RcIdentModel.ID_SIZE; lia).
  cbn [Nat.sub nth RcIdentModel.le16]. rewrite !d5_bz_zb. rewrite !Z.mod_mod by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma d5_rec_fw : forall inp i, SlotModel.rec_r inp i = 1 -> SlotModel.rec_addr inp i = RcIdentModel.ADDR_FIRMWARE ->
  4 <= SlotModel.rec_k inp i /\
  (forall j, (j < 4)%nat -> 0 <= RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) j) <= 9) /\
  RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id inp (S i)) 2) = 1 /\
  RcIdentModel.fw_milli (SlotModel.rec_id inp (S i)) = RcIdentModel.fw_value (SlotModel.rec_pl inp i).
Proof.
intros inp i Hr Ha. unfold SlotModel.rec_r in Hr. cbn [SlotModel.rec_id]. rewrite Ha in Hr |- *.
destruct (d5_ing_fw (SlotModel.rec_id inp i) (SlotModel.rec_pl inp i) (SlotModel.rec_id_length inp i) Hr)
  as (E1 & E2 & E3 & E4).
pose proof (SlotModel.rec_pl_length inp i) as PL. pose proof (SlotModel.rec_k_range inp i) as KR.
split; [lia|]. split; [|split; [exact E3 | exact E4]].
intros j Hj. split; [unfold RcIdentModel.bz; apply bv_unsigned_in_range | apply d5_digits; [exact E2 | exact Hj | lia]].
Qed.

Lemma d5_rec_hw_keep : forall inp i, SlotModel.rec_addr inp i = RcIdentModel.ADDR_FIRMWARE ->
  SlotModel.rec_hw inp (S i) = SlotModel.rec_hw inp i.
Proof. intros inp i H. cbn [SlotModel.rec_hw]. rewrite H. reflexivity. Qed.

(* A byte of a list of bytes, as garr8 reads it. *)
Lemma d5_nth_map : forall (l : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = RcIdentModel.bz (RcIdentModel.nthb l j).
Proof.
intros l. induction l as [|b l IH]; intros [|j]; cbn [map nth]; try reflexivity.
rewrite IH. reflexivity.
Qed.

(* What reac_identity_fw_str writes for a firmware value of four decimal digits: "a.bcd" and the NUL. *)
Lemma d5_fw_bytes : forall a b c d, 0 <= a <= 9 -> 0 <= b <= 9 -> 0 <= c <= 9 -> 0 <= d <= 9 ->
  reac_identity_fw_str.fw_bytes (a * 1000 + b * 100 + c * 10 + d) = [48 + a; 46; 48 + b; 48 + c; 48 + d; 0].
Proof.
intros a b c d Ha Hb Hc Hd. unfold reac_identity_fw_str.fw_bytes.
rewrite reac_identity_fw_str_c.reac_identity_fw_str_c3_short by lia.
replace ((a * 1000 + b * 100 + c * 10 + d) / 1000) with a by (Z.div_mod_to_equations; lia).
replace ((a * 1000 + b * 100 + c * 10 + d) mod 1000 / 100) with b by (Z.div_mod_to_equations; lia).
replace ((a * 1000 + b * 100 + c * 10 + d) mod 1000 / 10 mod 10) with c by (Z.div_mod_to_equations; lia).
replace ((a * 1000 + b * 100 + c * 10 + d) mod 1000 mod 10) with d by (Z.div_mod_to_equations; lia).
cbn [app map]. unfold IdentSpec.dg. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma d5_fw_L : forall v, 0 <= v <= 9999 -> reac_identity_fw_str_c.L v = 5.
Proof.
intros v Hv. rewrite (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v ltac:(lia))).
rewrite (proj2 (Z.ltb_lt v 10000)) by lia. reflexivity.
Qed.

(* ---- the symbolic states of the four runs ---------------------------------------------------------------------
   Atoms 0..31 are the registers at +0x730 (x9 = s1 = mf, x15 = a5 = the shadow base, x22 = s6 = rec_k,
   x23 = s7 = has_fw of `again`, x26 = s10 = its firmware value, x27 = s11 = pl); atom 32 is &s = SF+192 (mf+144),
   atom 33 the frame's shadow address (mf+160), atoms 34..37 the payload bytes pl[0..3]. *)
Definition d5_SB : Z := 0x7fff8000.
(* The machine frame: mf+40 is written (0x813d4), mf+144 and mf+160 are read. *)
Definition d5_rmf : YP09.region := YP09.mkRegion (Some 9%nat) 40 168 40 48
  [YP09.mkChunk 144 (CVal 8 (SOff 32 0)); YP09.mkChunk 160 (CVal 8 (SOff 33 0))].
(* The first four bytes of the payload copy. *)
Definition d5_rpl : YP09.region := YP09.mkRegion (Some 27%nat) 0 4 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SOff 35 0));
   YP09.mkChunk 2 (CVal 1 (SOff 36 0)); YP09.mkChunk 3 (CVal 1 (SOff 37 0))].
(* The shadow byte of `s` (shadow(SF) + 24), written at 0x81418 and 0x81544. *)
Definition d5_rsh : YP09.region := YP09.mkRegion (Some 33%nat) 24 25 24 25 [].
(* `s` after reac_identity_fw_str: pl[0] + '0', '.', pl[1..3] + '0', NUL. *)
Definition d5_rs : YP09.region := YP09.mkRegion (Some 32%nat) 0 6 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 34 48)); YP09.mkChunk 1 (CVal 1 (SLit 46)); YP09.mkChunk 2 (CVal 1 (SOff 35 48));
   YP09.mkChunk 3 (CVal 1 (SOff 36 48)); YP09.mkChunk 4 (CVal 1 (SOff 37 48)); YP09.mkChunk 5 (CVal 1 (SLit 0))].
(* The digit sum the code computes at 0x813e4 .. 0x81408; the start state's alias makes it atom 26. *)
Definition d5_sum : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 34 0) (SLit 1000)) (SMd M_MUL (SOff 35 0) (SLit 100)))
    (SMd M_MUL (SOff 36 0) (SLit 10))) (SOff 37 0).
Definition d5_GA : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (15%nat, mkAF d5_SB d5_SB 0);
    (22%nat, mkAF 4 255 0); (23%nat, mkAF 1 1 0); (27%nat, HPTR 0);
    (32%nat, HPTR 3); (33%nat, mkAF d5_SB (d5_SB + 2 ^ 44) 0);
    (34%nat, mkAF 0 9 0); (35%nat, mkAF 0 9 0); (36%nat, mkAF 0 9 0); (37%nat, mkAF 0 9 0) ].
Definition d5_ssA : sstate := mkSS 0x730 sr_atoms [d5_rmf; d5_rpl] None (mkFacts d5_GA [] [(d5_sum, SOff 26 0)]).
Definition d5_Bx : sv := SOff 15 0.
Definition d5_Bspan : Z * Z := (d5_SB, d5_SB + 2 ^ 44 - 1).
Definition d5_SH : list shent := [mkSHE 27 0 4].
Definition d5_extra (sf p0 p1 p2 p3 : Z) : list word :=
  map (Z_to_bv 64) [sf + 192; shadow_addr sf; p0; p1; p2; p3].

(* The linear form of the digit sum (the engine's lin_nf, by computation). *)
Lemma d5_sum_lin : lin_nf d5_sum = Some ([(34%nat, 1000); (35%nat, 100); (36%nat, 10); (37%nat, 1)], 0).
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition d5_E (regs : bvmap 5 word) (sf p0 p1 p2 p3 : Z) : env := Eimg (Ereg regs (d5_extra sf p0 p1 p2 p3)).
Lemma d5_E_reg : forall regs extra (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof. intros regs extra n r Hn Hr. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs extra n r Hr). Qed.
Lemma d5_E_extra : forall regs sf p0 p1 p2 p3 (j : nat), (j < 6)%nat ->
  ew (d5_E regs sf p0 p1 p2 p3) (32 + j) = nth j (d5_extra sf p0 p1 p2 p3) (Z_to_bv 64 0).
Proof. intros regs sf p0 p1 p2 p3 j Hj. unfold d5_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma d5_UA : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma d5_VB : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v.
Proof. intros E n v H Hv. cbn [base_val]. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma d5_den : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* The start state of run A1 at +0x730 holds of a concrete state with the facts the cut inv_caseF gives. *)
Lemma d5_entryA : forall (W : world SEGS) (regs : bvmap 5 word) mem mf sf pl rk fw p0 p1 p2 p3,
  getr regs 2 = w64 mf -> getr regs 9 = w64 mf -> getr regs 15 = w64 SHADOW_OFF ->
  getr regs 22 = w64 rk -> getr regs 23 = w64 1 -> getr regs 26 = w64 fw -> getr regs 27 = w64 pl ->
  2 ^ 46 <= mf <= 2 ^ 47 -> mf mod 32 = 0 -> 4 <= rk <= 255 ->
  4096 <= sf -> sf + 1024 <= 140737479966720 -> sf mod 8 = 0 ->
  4096 <= pl -> pl + 4 <= mf -> pl + 4 <= 140737479966720 ->
  0 <= p0 <= 9 -> 0 <= p1 <= 9 -> 0 <= p2 <= 9 -> 0 <= p3 <= 9 ->
  fw = p0 * 1000 + p1 * 100 + p2 * 10 + p3 ->
  (forall q, mf + 40 <= q < mf + 48 -> apresent (w_H W) mem q) ->
  val_mem SEGS (mrestrict (w_H W) mem) (mf + 144) 8 (sf + 192) ->
  val_mem SEGS (mrestrict (w_H W) mem) (mf + 160) 8 (shadow_addr sf) ->
  val_mem SEGS (mrestrict (w_H W) mem) (pl + 0) 1 p0 -> val_mem SEGS (mrestrict (w_H W) mem) (pl + 1) 1 p1 ->
  val_mem SEGS (mrestrict (w_H W) mem) (pl + 2) 1 p2 -> val_mem SEGS (mrestrict (w_H W) mem) (pl + 3) 1 p3 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF pl 4 ->
  pl + 4 <= kLowShadowBeg \/ kHighMemBeg <= pl ->
  st_ok_pi SEGS VAL (d5_E regs sf p0 p1 p2 p3) d5_ssA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x730)) mem (seg_rom SEGS))) /\
  sh_ok SEGS d5_Bx d5_SH (d5_E regs sf p0 p1 p2 p3) (mrestrict (w_H W) mem).
Proof.
intros W regs mem mf sf pl rk fw p0 p1 p2 p3 R2 R9 R15 R22 R23 R26 R27 Hmf Hmf32 Hrk Hsf1 Hsf2 Hsf8 Hpl1 Hpl2 Hpl3
  Hp0 Hp1 Hp2 Hp3 Hfw Hpres V144 V160 B0 B1 B2 B3 Hra Happ.
set (E := d5_E regs sf p0 p1 p2 p3).
assert (E2 : ew E 2 = Z_to_bv 64 mf) by (subst E; unfold d5_E; rewrite (d5_E_reg regs _ 2 2%bv) by (reflexivity || lia); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 mf) by (subst E; unfold d5_E; rewrite (d5_E_reg regs _ 9 9%bv) by (reflexivity || lia); exact R9).
assert (E15 : ew E 15 = Z_to_bv 64 SHADOW_OFF) by (subst E; unfold d5_E; rewrite (d5_E_reg regs _ 15 15%bv) by (reflexivity || lia); exact R15).
assert (E22 : ew E 22 = Z_to_bv 64 rk) by (subst E; unfold d5_E; rewrite (d5_E_reg regs _ 22 22%bv) by (reflexivity || lia); exact R22).
assert (E23 : ew E 23 = Z_to_bv 64 1) by (subst E; unfold d5_E; rewrite (d5_E_reg regs _ 23 23%bv) by (reflexivity || lia); exact R23).
assert (E26 : ew E 26 = Z_to_bv 64 fw) by (subst E; unfold d5_E; rewrite (d5_E_reg regs _ 26 26%bv) by (reflexivity || lia); exact R26).
assert (E27 : ew E 27 = Z_to_bv 64 pl) by (subst E; unfold d5_E; rewrite (d5_E_reg regs _ 27 27%bv) by (reflexivity || lia); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (sf + 192)) by exact (d5_E_extra regs sf p0 p1 p2 p3 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (shadow_addr sf)) by exact (d5_E_extra regs sf p0 p1 p2 p3 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 p0) by exact (d5_E_extra regs sf p0 p1 p2 p3 2 ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 p1) by exact (d5_E_extra regs sf p0 p1 p2 p3 3 ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 p2) by exact (d5_E_extra regs sf p0 p1 p2 p3 4 ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 p3) by exact (d5_E_extra regs sf p0 p1 p2 p3 5 ltac:(lia)).
assert (Hsh : SHADOW_OFF + 4096 / 8 <= shadow_addr sf <= SHADOW_OFF + 140737479966720 / 8)
  by (unfold shadow_addr; split; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
unfold SHADOW_OFF in Hsh. change (4096 / 8) with 512 in Hsh. change (140737479966720 / 8) with 17592184995840 in Hsh.
split.
- rewrite restrict_mkst_fx. unfold d5_ssA. apply pa_entry_st_ok_full.
  + subst E. unfold d5_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold d5_rmf, d5_rpl. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (d5_VB E 9 mf E9) by lia. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ mf 144 8 (SOff 32 0) (sf + 192)); [exact (d5_den E 32 _ E32) | zside | zside | exact V144].
      -- apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 33 0) (shadow_addr sf)); [exact (d5_den E 33 _ E33) | zside | zside | exact V160].
    * rewrite (d5_VB E 27 pl E27) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      -- apply (chunk_ok_val SEGS E _ pl 0 1 (SOff 34 0) p0); [exact (d5_den E 34 _ E34) | zside | zside | exact B0].
      -- apply (chunk_ok_val SEGS E _ pl 1 1 (SOff 35 0) p1); [exact (d5_den E 35 _ E35) | zside | zside | exact B1].
      -- apply (chunk_ok_val SEGS E _ pl 2 1 (SOff 36 0) p2); [exact (d5_den E 36 _ E36) | zside | zside | exact B2].
      -- apply (chunk_ok_val SEGS E _ pl 3 1 (SOff 37 0) p3); [exact (d5_den E 37 _ E37) | zside | zside | exact B3].
  + apply pairwise_disjoint_of_extents. unfold d5_rmf, d5_rpl, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (d5_VB E 9 mf E9) by lia. rewrite (d5_VB E 27 pl E27) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hmf Hpl1 Hpl2. clear. intros. repeat split; lia.
  + split; [|split].
    * cbn [d5_GA f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite (d5_UA E 2 mf E2), (d5_UA E 9 mf E9), (d5_UA E 15 SHADOW_OFF E15), (d5_UA E 22 rk E22),
        (d5_UA E 23 1 E23), (d5_UA E 27 pl E27), (d5_UA E 32 _ E32), (d5_UA E 33 _ E33),
        (d5_UA E 34 p0 E34), (d5_UA E 35 p1 E35), (d5_UA E 36 p2 E36), (d5_UA E 37 p3 E37)
        by (unfold SHADOW_OFF; lia).
      change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (Hsf192 : (sf + 192) mod 8 = 0) by (rewrite Z.add_mod, Hsf8 by lia; reflexivity).
      unfold d5_SB, SHADOW_OFF in *.
      revert Hmf Hmf32 Hrk Hsf1 Hsf2 Hsf192 Hpl1 Hpl2 Hpl3 Hp0 Hp1 Hp2 Hp3 Hsh. clear. intros.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    * cbn [f_conds conds_ok]. exact I.
    * cbn [f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite (lin_nf_sound E d5_sum _ _ d5_sum_lin). cbn [lin_denot].
      rewrite (d5_UA E 34 p0 E34), (d5_UA E 35 p1 E35), (d5_UA E 36 p2 E36), (d5_UA E 37 p3 E37) by lia.
      rewrite (U_atom E 26 fw E26) by lia. unfold M64. rewrite Z.mod_small by lia. lia.
- unfold sh_ok, d5_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E d5_Bx 27 pl 4 pl 0 4 Hra).
  + unfold d5_Bx. apply (U_atom E 15 SHADOW_OFF E15). unfold SHADOW_OFF. lia.
  + apply (U_atom E 27 pl E27). lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ---- what each step of the segment keeps ---------------------------------------------------------------------
   The facts of the cuts live in three places: the machine stack from mf up (the machine frame and the
   prologue's saved words; the segment writes mf+40 .. mf+48 there), the heap blocks bl of the start state (the
   payload copy pl and the input block), and the side-stack frame (4, pos) at sf with its 128 shadow bytes, of
   which the segment writes the bytes ex (`s`, SF+192 .. SF+200, and its shadow byte shadow(sf) + 24). *)
Definition d5_prot (mf sf : Z) (bl : list (Z * Z)) (ex : Z -> Prop) (a : Z) : Prop :=
  ((mf <= a < 2 ^ 64) /\ ~ (mf + 40 <= a < mf + 48)) \/
  (exists b n, In (b, n) bl /\ b <= a < b + req_size n) \/
  ((sf <= a < sf + 1024 \/ shadow_addr sf <= a < shadow_addr sf + 128) /\ ~ ex a).
Definition d5_keep (mf sf : Z) (bl : list (Z * Z)) (ex : Z -> Prop) (W : world SEGS) (m : word -> option byte)
  (W' : world SEGS) (m' : word -> option byte) : Prop :=
  forall a, d5_prot mf sf bl ex a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a.
(* Where the three places lie: the frame and the blocks in application memory below mf, the frame's shadow
   in shadow memory. *)
Definition d5_geo (mf sf : Z) (bl : list (Z * Z)) : Prop :=
  4096 <= sf /\ sf + 1024 <= mf /\ sf mod 64 = 0 /\ kHighMemBeg <= mf /\ mf <= 2 ^ 47 /\
  (sf + 1024 <= kLowShadowBeg \/ kHighMemBeg <= sf) /\ shadow_addr sf + 128 <= kHighMemBeg /\
  (forall b n, In (b, n) bl -> 0 <= b /\ b + req_size n <= mf /\ (b + req_size n <= sf \/ sf + 1024 <= b) /\
     (b + req_size n <= kLowShadowBeg \/ kHighMemBeg <= b)).
Lemma d5_keep_refl : forall mf sf bl ex W m, d5_keep mf sf bl ex W m W m.
Proof. intros mf sf bl ex W m a _. reflexivity. Qed.
Lemma d5_keep_trans : forall mf sf bl ex W1 m1 W2 m2 W3 m3,
  d5_keep mf sf bl ex W1 m1 W2 m2 -> d5_keep mf sf bl ex W2 m2 W3 m3 -> d5_keep mf sf bl ex W1 m1 W3 m3.
Proof. intros mf sf bl ex W1 m1 W2 m2 W3 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma d5_keep_mono : forall mf sf bl (ex ex' : Z -> Prop) W m W' m',
  (forall a, ex a -> ex' a) -> d5_keep mf sf bl ex W m W' m' -> d5_keep mf sf bl ex' W m W' m'.
Proof.
intros mf sf bl ex ex' W m W' m' Hex H a Ha. apply H.
destruct Ha as [Ha | [Ha | (Ha & Hn)]]; [left; exact Ha | right; left; exact Ha |].
right; right. split; [exact Ha | intros X; exact (Hn (Hex a X))].
Qed.
(* The shadow of the frame lies between the application memory below and above it. *)
Lemma d5_sh_bounds : forall sf, 4096 <= sf -> sf + 1024 <= 140737479966720 ->
  kLowShadowBeg < shadow_addr sf /\ shadow_addr sf + 128 <= kHighMemBeg.
Proof.
intros sf H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg.
assert (4096 / 8 <= sf / 8) by (apply Z.div_le_mono; lia).
assert ((sf + 1024) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
assert ((sf + 1024) / 8 = sf / 8 + 128) by (replace (sf + 1024) with (sf + 128 * 8) by lia; apply Z.div_add; lia).
change (4096 / 8) with 512 in *. change (140737479966720 / 8) with 17592184995840 in *. lia.
Qed.
(* A run of the engine writes only its regions' windows. *)
Lemma d5_keep_run : forall mf sf bl (ex : Z -> Prop) (W : world SEGS) m m' E rs,
  d5_geo mf sf bl -> kLowShadowBeg < shadow_addr sf ->
  (forall a, ex a -> sf <= a < sf + 1024 \/ shadow_addr sf <= a < shadow_addr sf + 128) ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E rs a -> (mf + 40 <= a < mf + 48) \/ ex a) ->
  d5_keep mf sf bl ex W m W m'.
Proof.
intros mf sf bl ex W m m' E rs (G1 & G2 & _ & G3 & G4 & G5 & G6 & G7) Gs Hex HF Hw a Ha.
assert (Hr : 0 <= a < 2 ^ 64).
{ destruct Ha as [(Ha & _) | [(b & n & Hin & Hb) | ([Ha | Ha] & _)]]; [lia | | lia |].
  - destruct (G7 b n Hin) as (B1 & B2 & _). lia.
  - unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_pos sf 8 ltac:(lia) ltac:(lia)). unfold kHighMemBeg in G6. lia. }
apply aview_eq_of. apply HF. rewrite unsigned_lit_small by exact Hr. intros Hin.
destruct (Hw a Hin) as [Hm | He].
- destruct Ha as [(_ & Hn) | [(b & n & Hb & Hab) | ([Ha | Ha] & _)]]; [exact (Hn Hm) | | lia |].
  + destruct (G7 b n Hb) as (_ & B2 & _). lia.
  + unfold kHighMemBeg in *. lia.
- pose proof (Hex a He) as Hz.
  destruct Ha as [(Ha & _) | [(b & n & Hb & Hab) | (_ & Hn)]]; [| | exact (Hn He)].
  + destruct Hz as [Hz | Hz]; [lia | unfold kHighMemBeg in *; lia].
  + destruct (G7 b n Hb) as (_ & _ & B3 & B4). unfold kLowShadowBeg, kHighMemBeg in *. destruct Hz as [Hz | Hz]; lia.
Qed.
(* What a fact over kept bytes keeps. *)
Lemma d5_tr_val : forall mf sf bl ex W m W' m' a n v,
  d5_keep mf sf bl ex W m W' m' -> (forall k, 0 <= k < Z.of_nat n -> d5_prot mf sf bl ex (a + k)) ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros mf sf bl ex W m W' m' a n v HK Hp Hv.
apply (val_mem_moved SEGS (w_H W) (w_H W') m m' a a n v); [|exact Hv].
intros k Hk. apply HK. apply Hp. exact Hk.
Qed.
Lemma d5_tr_garr8 : forall mf sf bl ex W m W' m' a l,
  d5_keep mf sf bl ex W m W' m' -> (forall x, a <= x < a + Z.of_nat (length l) -> d5_prot mf sf bl ex x) ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W') m') a l.
Proof.
intros mf sf bl ex W m W' m' a l HK Hp Hg. apply (garr8_frame SEGS _ _ a l Hg).
intros x Hx. apply (mbyte_of_aview SEGS). apply HK. apply Hp. exact Hx.
Qed.
Lemma d5_tr_zero : forall mf sf bl ex W m W' m' a len,
  d5_keep mf sf bl ex W m W' m' -> (forall i, 0 <= i < len / 8 -> d5_prot mf sf bl ex (shadow_of_addr SHADOW_OFF a + i)) ->
  zero_shadow (aview SEGS (w_H W) m) SHADOW_OFF a len -> zero_shadow (aview SEGS (w_H W') m') SHADOW_OFF a len.
Proof. intros mf sf bl ex W m W' m' a len HK Hp Hz i Hi. rewrite (HK _ (Hp i Hi)). exact (Hz i Hi). Qed.
Lemma d5_tr_blk : forall mf sf bl ex W m W' m' a n,
  d5_keep mf sf bl ex W m W' m' ->
  (forall i, 0 <= i < (n + 7) / 8 -> d5_prot mf sf bl ex (shadow_of_addr SHADOW_OFF a + i)) ->
  block_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n -> block_shadow (aview SEGS (w_H W') m') SHADOW_OFF a n.
Proof.
intros mf sf bl ex W m W' m' a n HK Hp (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite (HK _ (Hp i Hi)). exact (H3 i Hi).
Qed.
(* The bytes the segment writes in the frame: `s` (SF+192, 8 bytes) and its shadow byte. *)
Definition d5_ex (sf : Z) (a : Z) : Prop := (sf + 192 <= a < sf + 200) \/ a = shadow_addr sf + 24.
Lemma d5_prot_st : forall mf sf bl ex a, mf <= a < 2 ^ 64 -> ~ (mf + 40 <= a < mf + 48) -> d5_prot mf sf bl ex a.
Proof. intros mf sf bl ex a H1 H2. left. split; [exact H1 | exact H2]. Qed.
Lemma d5_prot_bl : forall mf sf bl ex b n a, In (b, n) bl -> b <= a < b + req_size n -> d5_prot mf sf bl ex a.
Proof. intros mf sf bl ex b n a Hin Ha. right. left. exists b, n. split; [exact Hin | exact Ha]. Qed.
Lemma d5_sh_lo : forall sf, 0 <= sf -> kLowShadowBeg < shadow_addr sf.
Proof. intros sf H. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg. pose proof (Z.div_pos sf 8 H ltac:(lia)). lia. Qed.
Lemma d5_prot_fr : forall mf sf bl a, d5_geo mf sf bl -> sf <= a < sf + 1024 -> ~ (sf + 192 <= a < sf + 200) ->
  d5_prot mf sf bl (d5_ex sf) a.
Proof.
intros mf sf bl a (G1 & G2 & _ & _ & _ & G5 & G6 & _) Ha Hn. right. right. split; [left; exact Ha|].
pose proof (d5_sh_lo sf ltac:(lia)) as S1.
intros [X | X]; [exact (Hn X)|]. subst a. unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma d5_prot_fsh : forall mf sf bl j, d5_geo mf sf bl -> 0 <= j < 128 -> j <> 24 ->
  d5_prot mf sf bl (d5_ex sf) (shadow_addr sf + j).
Proof.
intros mf sf bl j (G1 & G2 & _ & _ & _ & G5 & G6 & _) Hj Hj24. right. right. split; [right; lia|].
pose proof (d5_sh_lo sf ltac:(lia)) as S1.
intros [X | X]; [| lia]. unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma d5_sh_off : forall sf c, sf mod 64 = 0 -> c mod 8 = 0 -> shadow_of_addr SHADOW_OFF (sf + c) = shadow_addr sf + c / 8.
Proof.
intros sf c Hs Hc. unfold shadow_of_addr, shadow_addr.
pose proof (Z.div_mod sf 64 ltac:(lia)) as D. rewrite Hs, Z.add_0_r in D.
pose proof (Z.div_mod c 8 ltac:(lia)) as D2. rewrite Hc, Z.add_0_r in D2.
rewrite D, D2. replace (64 * (sf / 64) + 8 * (c / 8)) with ((8 * (sf / 64) + c / 8) * 8) by lia.
replace (64 * (sf / 64)) with ((8 * (sf / 64)) * 8) by lia. rewrite !Z.div_mul by lia. lia.
Qed.
(* The environments of the later runs agree with the start one on the atoms below 40. *)
Lemma d5_ew_extK : forall E K ws n, (n < K)%nat -> ew (extK E K ws) n = ew E n.
Proof.
intros E K ws. revert E K. induction ws as [|w ws IH]; intros E K n Hn; cbn [extK]; [reflexivity|].
rewrite IH by lia. cbn [ew ewset]. destruct (Nat.eqb_spec n K); [lia | reflexivity].
Qed.
(* A byte a region's one-byte chunk holds. *)
Lemma d5_region_byte : forall E (H : word -> bool) mem (n : nat) lo hi wlo whi cs off e v,
  YP09.region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  In (YP09.mkChunk off (CVal 1 e)) cs -> bv_unsigned (byte_of_word (sv_denot E e) 0) = v ->
  aview SEGS H mem (base_val E (Some n) + off) = Some v.
Proof.
intros E H mem n lo hi wlo whi cs off e v (_ & _ & _ & HCH) Hin He.
cbn [YP09.r_chunks YP09.r_base] in HCH. pose proof (proj1 (Forall_forall _ _) HCH _ Hin) as Hc.
destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2.
injection Hb1 as Hb1. subst b. rewrite Z.add_0_r in Hb2. unfold aview. rewrite Hb2. cbn [option_map]. rewrite He. reflexivity.
Qed.
(* The shadow entries of pl[0 .. 4) in a later state (the shadow base is atom 15, pl atom 27). *)
Lemma d5_shok : forall (Ex : env) (W : world SEGS) mem pl,
  ew Ex 15 = Z_to_bv 64 SHADOW_OFF -> ew Ex 27 = Z_to_bv 64 pl -> 0 <= pl -> pl + 4 <= 2 ^ 64 ->
  (pl + 4 <= kLowShadowBeg \/ kHighMemBeg <= pl) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF pl 4 ->
  sh_ok SEGS d5_Bx d5_SH Ex (rd W mem).
Proof.
intros Ex W mem pl E15 E27 H0 H1 Happ Hra. unfold sh_ok, d5_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem Ex d5_Bx 27 pl 4 pl 0 4 Hra).
- unfold d5_Bx. apply (U_atom Ex 15 SHADOW_OFF E15). unfold SHADOW_OFF. lia.
- apply (U_atom Ex 27 pl E27). lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma d5_prot_fr0 : forall mf sf bl (ex : Z -> Prop) a, sf <= a < sf + 1024 -> ~ ex a -> d5_prot mf sf bl ex a.
Proof. intros mf sf bl ex a Ha Hn. right; right. split; [left; exact Ha | exact Hn]. Qed.
Lemma d5_prot_fsh0 : forall mf sf bl (ex : Z -> Prop) j, 0 <= j < 128 -> ~ ex (shadow_addr sf + j) ->
  d5_prot mf sf bl ex (shadow_addr sf + j).
Proof. intros mf sf bl ex j Hj Hn. right; right. split; [right; lia | exact Hn]. Qed.
Lemma d5_den_off : forall (Ex : env) n z v, bv_unsigned (ew Ex n) = v -> 0 <= v + z < 2 ^ 64 ->
  sv_denot Ex (SOff n z) = Z_to_bv 64 (v + z).
Proof.
intros Ex n z v Hv Hr. apply bv_eq. rewrite denot_SOff, Hv, (zcanon_id (v + z)) by (unfold M64; lia).
symmetry. apply unsigned_lit_small. exact Hr.
Qed.
(* The region of the shadow byte of `s` (shadow(sf) + 24), which the segment writes twice. *)
Lemma d5_rsh_ok : forall (Ex : env) (W : world SEGS) mem sf,
  bv_unsigned (ew Ex 33) = shadow_addr sf -> 4096 <= sf -> sf + 1024 <= 140737479966720 ->
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr sf + i)) ->
  region_ok SEGS Ex (rd W mem) d5_rsh.
Proof.
intros Ex W mem sf E33 Hs1 Hs2 Hpres.
pose proof (d5_sh_bounds sf Hs1 Hs2) as (S1 & S2). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold d5_rsh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E33. split; [unfold kLowShadowBeg in S1; lia|]. split; [unfold kHighMemBeg in S2; lia|].
split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
Qed.
(* The region of `s` after reac_identity_fw_str: "p0 . p1 p2 p3" and the NUL. *)
Lemma d5_rs_ok : forall (Ex : env) (W : world SEGS) mem sf p0 p1 p2 p3,
  bv_unsigned (ew Ex 32) = sf + 192 -> bv_unsigned (ew Ex 34) = p0 -> bv_unsigned (ew Ex 35) = p1 ->
  bv_unsigned (ew Ex 36) = p2 -> bv_unsigned (ew Ex 37) = p3 ->
  0 <= p0 <= 9 -> 0 <= p1 <= 9 -> 0 <= p2 <= 9 -> 0 <= p3 <= 9 -> 0 <= sf -> sf + 1024 <= 2 ^ 64 ->
  garr8 SEGS (rd W mem) (sf + 192) [48 + p0; 46; 48 + p1; 48 + p2; 48 + p3; 0] ->
  region_ok SEGS Ex (rd W mem) d5_rs.
Proof.
intros Ex W mem sf p0 p1 p2 p3 E32 E34 E35 E36 E37 H0 H1 H2 H3 Hs1 Hs2 HG.
assert (V : forall j v, (j < 6)%nat -> nth j [48 + p0; 46; 48 + p1; 48 + p2; 48 + p3; 0] 0 = v ->
  val_mem SEGS (rd W mem) (sf + 192 + Z.of_nat j) 1 v).
{ intros j v Hj <-. exact (proj1 (HG j ltac:(cbn [length]; lia))). }
unfold d5_rs, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS Ex _ (sf + 192) 0 1 (SOff 34 48) (48 + p0));
  [rewrite (d5_den_off Ex 34 48 p0 E34) by lia; f_equal; lia | zside | zside | exact (V 0%nat _ ltac:(lia) eq_refl)].
- apply (chunk_ok_val SEGS Ex _ (sf + 192) 1 1 (SLit 46) 46);
  [reflexivity | zside | zside | exact (V 1%nat _ ltac:(lia) eq_refl)].
- apply (chunk_ok_val SEGS Ex _ (sf + 192) 2 1 (SOff 35 48) (48 + p1));
  [rewrite (d5_den_off Ex 35 48 p1 E35) by lia; f_equal; lia | zside | zside | exact (V 2%nat _ ltac:(lia) eq_refl)].
- apply (chunk_ok_val SEGS Ex _ (sf + 192) 3 1 (SOff 36 48) (48 + p2));
  [rewrite (d5_den_off Ex 36 48 p2 E36) by lia; f_equal; lia | zside | zside | exact (V 3%nat _ ltac:(lia) eq_refl)].
- apply (chunk_ok_val SEGS Ex _ (sf + 192) 4 1 (SOff 37 48) (48 + p3));
  [rewrite (d5_den_off Ex 37 48 p3 E37) by lia; f_equal; lia | zside | zside | exact (V 4%nat _ ltac:(lia) eq_refl)].
- apply (chunk_ok_val SEGS Ex _ (sf + 192) 5 1 (SLit 0) 0);
  [reflexivity | zside | zside | exact (V 5%nat _ ltac:(lia) eq_refl)].
Qed.

Section c.
(* The Section of the contract and of the boundary layer, in the same order (LLVMFuzzerTestOneInput_inv.v). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LS : lib_shape.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* The contract's hypotheses the segment uses, with LLVMFuzzerTestOneInput.v's statements and in its order. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
(* reac_identity_fw_str's post-condition says nothing of the meter, so the cut's two meter facts cross the call
   with HMT0 (mo_le MT Sc S2 0). *)
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis HCHK : check_str.tcheck_str_spec B.
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.

#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_CASEF := (inv_caseF B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_TAIL := (inv_tail B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JR g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]).

(* The contract's pre-condition of the entry state, the parts the segment reads. *)
Lemma d5_pre : forall g, EPRE g ->
  afn_pre SEGS B LLVMF_STK (e_ly g) (e_S g) (e_W g) (e_regs g) (e_mem g) (e_md g) [] /\ raZ (e_regs g) = RA_LLVMF /\
  ((e_n g = 0 /\ e_p g = A_EMPTY) \/ (0 < e_n g < 2 ^ 26 /\ In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)))) /\
  e_n g = Z.of_nat (length (e_pl g)) /\ frames (e_S g) = [] /\
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H (e_W g)) (e_mem g)).
Proof.
intros g (H1 & H2 & _ & _ & H5 & H6 & _ & H8 & _ & _ & H11 & _).
split; [exact H1|]. split; [exact H2|]. split; [exact H5|]. split; [exact H6|]. split; [exact H8 | exact H11].
Qed.
(* A journal keeps the frame area's base (layout_le keeps ly_F). *)
Lemma d5_fa : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos,
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
Lemma d5_fs4 : fs_frame_bytes 4 = 1024.
Proof. reflexivity. Qed.
(* reac_identity_fw_str writes `s` only. *)
Lemma d5_keep_fw : forall mf sf bl (ex : Z -> Prop) lyc Sc (W : world SEGS) memc W2 mem2 pos STKf,
  d5_geo mf sf bl -> alloc_ceiling <= mf ->
  tcj_kept B STKf lyc Sc W memc W2 mem2 mf (fun a => sf + 192 <= a < sf + 192 + 6) ->
  (forall b n, In (b, n) bl -> In (b, n) (ablocks B lyc Sc)) ->
  In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = sf ->
  (forall a, sf + 192 <= a < sf + 198 -> ex a) ->
  d5_keep mf sf bl ex W memc W2 mem2.
Proof.
intros mf sf bl ex lyc Sc W memc W2 mem2 pos STKf (G1 & G2 & _ & G3 & G4 & _ & G6 & G7) Hceil (K1 & K2 & _ & K4 & _) Hbl Hin Hfa Hex a Ha.
destruct Ha as [(Ha & Hn) | [(b & n & Hb & Hab) | (Ha & Hn)]].
- apply K1; lia.
- destruct (G7 b n Hb) as (B1 & B2 & B3 & _). replace a with (b + (a - b)) by lia.
  apply (K2 b n (a - b) (Hbl b n Hb)); [lia|]. lia.
- apply (K4 4 pos a Hin).
  + unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, d5_fs4. change (1024 / 8) with 128. lia.
  + intros X. apply Hn. apply Hex. lia.
Qed.
(* check_str writes only its own stack window below mf. *)
Lemma d5_keep_chk : forall mf sf bl (ex : Z -> Prop) STK1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 pos,
  d5_geo mf sf bl -> alloc_ceiling <= mf ->
  ajournal SEGS B STK1 mf [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  (forall b n, In (b, n) bl -> In (b, n) (ablocks B lyc Sc) /\ In (b, n) (ablocks B ly2 S2)) ->
  In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = sf ->
  d5_keep mf sf bl ex W memc W2 mem2.
Proof.
intros mf sf bl ex STK1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 pos (G1 & G2 & _ & G3 & G4 & _ & G6 & G7) Hceil
  (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _) Hbl Hin Hfa a Ha.
assert (NF : forall x, ~ inFP [] x) by (intros x (r & Hr & _); destruct Hr).
destruct Ha as [(Ha & Hn) | [(b & n & Hb & Hab) | (Ha & Hn)]].
- apply F1; lia.
- destruct (G7 b n Hb) as (B1 & B2 & B3 & _). destruct (Hbl b n Hb) as [Hb1 Hb2].
  replace a with (b + (a - b)) by lia. apply (F2 b n (a - b) Hb1 Hb2); [lia | apply NF].
- apply (F4 4 pos a Hin); [|apply NF].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, d5_fs4. change (1024 / 8) with 128. lia.
Qed.
(* check_str keeps every byte from its caller's sp up (the machine frame mf+40 .. mf+168 too). *)
Lemma d5_chk_st : forall STK1 mf lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1,
  ajournal SEGS B STK1 mf [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 -> alloc_ceiling <= mf ->
  forall a, mf <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros STK1 mf lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _) Hc a Ha.
apply F1; lia.
Qed.
(* A keep with a smaller set of written bytes, as one with the segment's set d5_ex. *)
Ltac d5_km K :=
  refine (d5_keep_mono _ _ _ _ _ _ _ _ _ _ K); unfold d5_ex;
  let a := fresh "a" in let Hx := fresh "Hx" in intros a Hx; cbv beta in Hx |- *;
  first [ contradiction | right; exact Hx | left; clear - Hx; lia ].
(* YCbq.aj_call without its symbolic state: a callee in the afn_pre form, called with sp = sp0 + o. *)
Lemma d5_aj_call : forall W (ms : machine_state) STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg ms mdc) (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK1 (spZ (ms_regs ms)) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
     aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr SEGS W (mkCfg ms mdc) (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
     ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
     aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
  HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
  try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
Lemma d5_m32_16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 32) with ((2 * q) * 16) by lia. apply Z.mod_mul. lia. Qed.
Lemma d5_m64_8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 64) with ((8 * q) * 8) by lia. apply Z.mod_mul. lia. Qed.
Lemma d5_div8 : forall sf x, sf mod 64 = 0 -> sf + 192 <= x < sf + 200 -> x / 8 = sf / 8 + 24.
Proof.
intros sf x H Hx. apply d5_m64_8 in H. pose proof (Z.div_mod sf 8 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
symmetry. apply (Z.div_unique x 8 (sf / 8 + 24) (x - sf - 192)); lia.
Qed.
(* What the entry's journal gives at any state of the segment. *)
Lemma d5_jr : forall g pos ly2 S2 (W : world SEGS) mem md k, JR g pos ly2 S2 W mem md k ->
  AR SEGS B ly2 S2 W mem md /\ frames S2 = (4, pos) :: frames (e_S g) /\ In (4, pos) (frames S2) /\
  frame_addr ly2 4 pos = SFa g pos /\ ly_top ly2 = ly_top (e_ly g) /\
  e_sp0 g mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= e_sp0 g /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g <= ly_top (e_ly g) <= 2 ^ 47 /\
  (forall a, e_sp0 g - LLVMF_STK <= a < e_sp0 g -> apresent (w_H W) mem a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (e_sp0 g - LLVMF_STK <= a < e_sp0 g) ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (e_W g)) (e_mem g) a).
Proof.
intros g pos ly2 S2 W mem md k HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
split; [exact HAR|]. split; [exact Hfrs|]. split; [rewrite Hfrs; left; reflexivity|].
split; [unfold SFa; exact (d5_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos HJ)|].
split; [destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et|].
split; [exact Hsp0al|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hpres | exact F1].
Qed.
(* The frame (4, pos) at sf: where it lies and that its bytes and shadow bytes are there. *)
Lemma d5_frame : forall ly S (W : world SEGS) mem md pos sf,
  AR SEGS B ly S W mem md -> In (4, pos) (frames S) -> frame_addr ly 4 pos = sf ->
  4096 <= sf /\ sf + 1024 <= alloc_ceiling /\ sf mod 64 = 0 /\ in_app sf 1024 /\
  (forall a, sf <= a < sf + 1024 -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr sf + i) /\ ~ aowned B ly S (shadow_addr sf + i)).
Proof.
intros ly S W mem md pos sf HAR Hin Hfa.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin) as (_ & Happ & Hb & Hs).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (H4096 & Hcl & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 4 pos HAR Hin) as (H64 & _).
rewrite Hfa, d5_fs4 in *. change (1024 / 8) with 128 in Hs.
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H64|]. split; [exact Happ|]. split; [exact Hb | exact Hs].
Qed.
(* What is present at any state of the segment: the frame, its shadow and the entry's stack window. *)
Lemma d5_state : forall g pos ly2 S2 (W : world SEGS) mem md k, JR g pos ly2 S2 W mem md k ->
  (forall j, 0 <= j < 128 -> apresent (w_H W) mem (shadow_addr (SFa g pos) + j)) /\
  (forall a, SFa g pos <= a < SFa g pos + 1024 -> apresent (w_H W) mem a) /\
  (forall a, e_sp0 g - LLVMF_STK <= a < e_sp0 g -> apresent (w_H W) mem a).
Proof.
intros g pos ly2 S2 W mem md k HJ.
destruct (d5_jr g pos ly2 S2 W mem md k HJ) as (HAR & _ & Hin & Hfa & _ & _ & _ & _ & _ & Hpres & _).
destruct (d5_frame ly2 S2 W mem md pos (SFa g pos) HAR Hin Hfa) as (_ & _ & _ & _ & Hfb & Hfs).
split; [intros j Hj; exact (proj1 (Hfs j Hj))|].
split; [intros a Ha; exact (proj1 (Hfb a Ha)) | exact Hpres].
Qed.

(* ---- the call of reac_identity_fw_str at 0x8142c: v, &s = SF+192, 8 ---------------------------------------- *)
Lemma d5_call_fw : forall g pos ly2 S2 (W : world SEGS) (regs : bvmap 5 word) mem md k mf v Q,
  JR g pos ly2 S2 W mem md k ->
  getr regs 1 = Z_to_bv 64 (BASE + 0xcbc) -> getr regs 2 = Z_to_bv 64 mf ->
  getr regs 10 = Z_to_bv 64 v -> getr regs 11 = Z_to_bv 64 (SFa g pos + 192) -> getr regs 12 = Z_to_bv 64 8 ->
  0 <= v <= 9999 -> mf mod 32 = 0 -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  aview SEGS (w_H W) mem (shadow_addr (SFa g pos) + 24) = Some 0 ->
  (forall W' c', reac_identity_fw_str.treac_identity_fw_str_post B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
     (e_mem g) (e_md g) [(4, pos)] ly2 S2 W mem k regs v (SFa g pos + 192) 8 W' c' -> SRr SEGS W' c' Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_identity_fw_str) regs mem md) Q.
Proof.
intros g pos ly2 S2 W regs mem md k mf v Q HJ R1 R2 R10 R11 R12 Hv Hmf32 Hmf Hsh HK.
destruct (d5_jr g pos ly2 S2 W mem md k HJ) as (HAR & _ & Hin & Hfa & _ & Hsp0al & Hsp0lo & Hsp0hi & _ & _ & _).
destruct (d5_frame ly2 S2 W mem md pos (SFa g pos) HAR Hin Hfa) as (Hf1 & Hf2 & Hf64 & _ & Hfb & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_LLVMF = 16736) by reflexivity.
assert (Hsp : spZ regs = mf) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
eapply SRr_bind;
[ apply (HFWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W mem md k regs
    v (SFa g pos + 192) 8 HJ)
| intros W' c' _ HP; exact (HK W' c' HP) ].
- rewrite R1. apply ret_ok_codeptr_v; lia.
- exact R10.
- exact R11.
- exact R12.
- lia.
- lia.
- lia.
- rewrite Hsp. apply d5_m32_16. exact Hmf32.
- rewrite Hsp. unfold reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK, reac_identity_fw_str.FW_FRAME, ESTACK. lia.
- rewrite Hsp. lia.
- intros _. unfold reac_identity_fw_str.fw_dest_ok. rewrite (reac_identity_fw_str.fw_n_short v) by lia.
  split; [|split].
  + intros a Ha. right. exists 4, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, d5_fs4. lia.
  + intros a Ha. destruct (Hfb a ltac:(lia)) as [Hp Ho]. split; [|split; [exact Hp | split; [exact Ho|]]].
    * right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite Hfa, d5_fs4. lia.
    * rewrite Hsp. unfold ESTACK. lia.
  + intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    rewrite (d5_div8 (SFa g pos) x Hf64) by lia. unfold shadow_addr in Hsh. rewrite <- Hsh. f_equal. lia.
Qed.

(* ---- the call of check_str at 0x8143c: 5, &s, 8 ----------------------------------------------------------- *)
Lemma d5_call_chk : forall g pos ly2 S2 (W : world SEGS) (ms : machine_state) md k mf p0 p1 p2 p3 Q,
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + AF_check_str)) (ms_mem ms) (seg_rom SEGS) ->
  JR g pos ly2 S2 W (ms_mem ms) md k -> EPRE g ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 0xccc) -> getr (ms_regs ms) 2 = Z_to_bv 64 mf ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 8 = w64 (e_sp0 g) ->
  getr (ms_regs ms) 10 = Z_to_bv 64 5 -> getr (ms_regs ms) 11 = Z_to_bv 64 (SFa g pos + 192) ->
  getr (ms_regs ms) 12 = Z_to_bv 64 8 ->
  mf mod 32 = 0 -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  0 <= p0 <= 9 -> 0 <= p1 <= 9 -> 0 <= p2 <= 9 -> 0 <= p3 <= 9 ->
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) (SFa g pos + 192) [48 + p0; 46; 48 + p1; 48 + p2; 48 + p3; 0] ->
  aview SEGS (w_H W) (ms_mem ms) (shadow_addr (SFa g pos) + 24) = Some 0 ->
  (forall W' c', (exists ly3 S3 regs3 mem3 md3,
      c' = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0xccc)) mem3 (seg_rom SEGS)) md3 /\
      JR g pos ly3 S3 W' mem3 md3 (k + 0) /\
      ajournal SEGS B check_str.CHECK_STR_STK mf [] ly2 S2 W (ms_mem ms) md [] ly3 S3 W' mem3 md3 0 /\
      aregs_preserved (ms_regs ms) regs3 /\ ly3 = ly2 /\ S3 = S2 /\ W' = W) -> SRr SEGS W' c' Q) ->
  SRr SEGS W (mkCfg ms md) Q.
Proof.
intros g pos ly2 S2 W ms md k mf p0 p1 p2 p3 Q Hms HJ Hpre R1 R2 R3 R4 R8 R10 R11 R12 Hmf32 Hmf V8 V16
  Hp0 Hp1 Hp2 Hp3 HG Hsh HK.
destruct (d5_jr g pos ly2 S2 W (ms_mem ms) md k HJ)
  as (HAR & _ & Hin & Hfa & Htop & Hsp0al & Hsp0lo & Hsp0hi & Hsp0top & Hpres & F1).
destruct (d5_frame ly2 S2 W (ms_mem ms) md pos (SFa g pos) HAR Hin Hfa) as (Hf1 & Hf2 & Hf64 & Hfapp & Hfb & _).
destruct (d5_pre g Hpre) as (HPRE0 & Hra0 & _ & _ & _ & Hro0).
pose proof HPRE0 as (_ & _ & Hra4 & _ & _ & _ & _ & Hch0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_LLVMF = 16736) by reflexivity.
assert (WC : check_str.CHECK_STR_STK = 8208) by reflexivity.
set (sf := SFa g pos) in *.
assert (Hsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z (ms_regs ms) = e_sp0 g) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
assert (HRA : 0 <= RA_LLVMF < 2 ^ 64) by (rewrite <- Hra0; unfold raZ; apply bv_unsigned_in_range).
assert (HS0 : 0 <= s0Z (e_regs g) < 2 ^ 64) by (unfold s0Z; apply bv_unsigned_in_range).
(* the frame-pointer chain the callee's pre-condition asks for: the entry's own record, then the caller's *)
assert (HCH : exists ch1, achain ly2 (aview SEGS (w_H W) (ms_mem ms)) mf (e_sp0 g) ch1).
{ destruct (Z_lt_le_dec (e_sp0 g) (ly_top ly2 - 16)) as [Hlt | Hge].
  - exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))].
    apply (achain_push ly2 (aview SEGS (w_H (e_W g)) (e_mem g))).
    + apply (achain_ly_top (e_ly g)); [exact Htop|]. exact Hch0.
    + rewrite Htop. lia.
    + intros a Ha. apply F1; lia.
    + exact (rdword_of_val_mem SEGS (w_H W) (ms_mem ms) _ _ V8 HRA).
    + exact (rdword_of_val_mem SEGS (w_H W) (ms_mem ms) _ _ V16 HS0).
    + rewrite Hra0 in Hra4. exact Hra4.
    + lia.
    + apply (Z.mod_divide (e_sp0 g) 8 ltac:(lia)). apply Z.mod_divide in Hsp0al; [|lia]. destruct Hsp0al as [q Hq].
      exists (2 * q). lia.
    + exact Hlt.
    + lia.
  - exists []. left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch1 & HCH).
subst sf. rewrite Hms. eapply SRr_bind.
{ rewrite <- Hms.
  eapply (d5_aj_call W ms LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 md k
    check_str.CHECK_STR_STK [] 0 (mf - e_sp0 g) (Z_to_bv 64 (BASE + 0xccc)) ch1
    (fun ly' S' W' _ _ _ => ly' = ly2 /\ S' = S2 /\ W' = W) HJ).
  - rewrite Hsp. lia.
  - replace (mf - e_sp0 g) with (mf + (- e_sp0 g)) by lia. rewrite Z.add_mod by lia.
    rewrite (d5_m32_16 mf Hmf32). replace ((- e_sp0 g) mod 16) with 0; [reflexivity|].
    apply Z.mod_divide in Hsp0al; [|lia]. destruct Hsp0al as [q Hq]. rewrite Hq.
    replace (- (q * 16)) with ((- q) * 16) by lia. rewrite Z.mod_mul by lia. reflexivity.
  - lia.
  - lia.
  - rewrite WC, WS in *. unfold STK_LLVMF, ASTACK in HSTK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
  - rewrite Hs0. replace (e_sp0 g + (mf - e_sp0 g)) with mf by lia. exact HCH.
  - intros HPRE. rewrite Hms.
    change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + AF_check_str)) (ms_mem ms) (seg_rom SEGS)) md)
      with (cfg_at SEGS check_str.A_check_strP (ms_regs ms) (ms_mem ms) md).
    eapply SRr_mono;
    [ apply (HCHK ly2 S2 W (ms_regs ms) (ms_mem ms) md ch1 5 (SFa g pos + 192) 8 HPRE) |].
    + apply (aro_unowned_of_arodata SEGS pa_relro_lo pa_relro_hi B).
      eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B); [exact HJ|]. apply HRO. exact Hro0.
    + exact R10.
    + exact R11.
    + exact R12.
    + lia.
    + lia.
    + intros _. unfold check_str.tcheck_str_ok.
      pose proof (frm_off_imgP B ly2 S2 W (ms_mem ms) md 4 pos HAR Hin) as Ho. rewrite Hfa, d5_fs4 in Ho.
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [| split; [| split; [| split; [| split]]]].
      * split; [lia|]. split.
        -- intros i Hi. destruct (HG (Z.to_nat i) ltac:(cbn [length]; lia)) as (Hv & Hr).
           exists (nth (Z.to_nat i) [48 + p0; 46; 48 + p1; 48 + p2; 48 + p3; 0] 0). split.
           ++ rewrite Z2Nat.id in Hv by lia. exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr).
           ++ assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
              destruct Hi' as [-> | [-> | [-> | [-> | ->]]]];
              [ change (Z.to_nat 0) with 0%nat | change (Z.to_nat 1) with 1%nat | change (Z.to_nat 2) with 2%nat
              | change (Z.to_nat 3) with 3%nat | change (Z.to_nat 4) with 4%nat ]; cbn [nth]; lia.
        -- intros _. destruct (HG 5%nat ltac:(cbn [length]; lia)) as (Hv & Hr). cbn [nth Z.of_nat] in Hv, Hr.
           exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr).
      * intros a Ha. rewrite Hsp, WC. lia.
      * unfold amem_range. unfold in_app in Hfapp. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg in *. lia.
      * intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
        rewrite (d5_div8 (SFa g pos) x Hf64) by lia. unfold shadow_addr in Hsh. rewrite <- Hsh. f_equal. lia.
      * apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W (ms_mem ms) md 4 pos (SFa g pos + 192) (5 + 1) HAR Hin);
        rewrite ?Hfa, ?d5_fs4; lia.
      * intros a Ha. assert (Hm : (SFa g pos + 192 + 5) mod 8 = 5).
        { rewrite Z.add_mod by lia. rewrite (Z.add_mod (SFa g pos) 192) by lia. rewrite (d5_m64_8 _ Hf64). reflexivity. }
        rewrite Hm in Ha. apply (aview_some_of_apresent SEGS). exact (proj1 (Hfb a ltac:(lia))).
    + cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & HJ1 & HP & HQ).
      exists ly', S', regs', mem', md'. split; [rewrite R1; reflexivity|].
      split; [exact HJ1|]. split; [exact HP | exact HQ].
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W' c' _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJs & HP3 & HQ3).
apply HK. exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [replace (e_sp0 g + (mf - e_sp0 g)) with mf in HJs by lia; exact HJs|].
split; [exact HP3 | exact HQ3].
Qed.

(* ---- the cut facts at the join, from those at the case's entry ------------------------------------------- *)
Lemma d5_prot_st8 : forall mf sf bl ex x, (mf <= x /\ x + 8 <= mf + 40) \/ (mf + 48 <= x /\ x + 8 <= 2 ^ 64) ->
  mf <= 2 ^ 47 -> forall k, 0 <= k < Z.of_nat 8 -> d5_prot mf sf bl ex (x + k).
Proof. intros mf sf bl ex x Hx Hm k Hk. change (Z.of_nat 8) with 8 in Hk. apply d5_prot_st; lia. Qed.
Lemma d5_ecommon : forall g pos mf ly2 S2 W2 regs2 mem2 md2 lyf Sf Wf regsf memf mdf kf bl,
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  d5_keep mf (SFa g pos) bl (d5_ex (SFa g pos)) W2 mem2 Wf memf -> d5_geo mf (SFa g pos) bl ->
  (forall b n, In (b, n) (ablocks B (e_ly g) (e_S g)) -> In (b, n) bl) ->
  getr regsf 2 = getr regs2 2 -> getr regsf 9 = getr regs2 9 -> getr regsf 8 = getr regs2 8 ->
  getr regsf 3 = getr regs2 3 -> getr regsf 4 = getr regs2 4 ->
  JR g pos lyf Sf Wf memf mdf kf ->
  ECOMMON g pos mf lyf Sf Wf regsf memf mdf.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 lyf Sf Wf regsf memf mdf kf bl HEC HK HG Hbl E2 E9 E8 E3 E4 HJf.
destruct (d5_jr g pos lyf Sf Wf memf mdf kf HJf) as (_ & _ & _ & _ & _ & _ & _ & Hsp0hi & _).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJf) as (Fd & Fs).
unfold ecommon in HEC |- *.
destruct HEC as (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & V16 & V64 & V192 & V168 & Vra & Vs0 & V24 & V32 & V40 & V48 &
  V56 & V64' & V72 & V80 & V88 & V96 & V104 & Vfl & Hpre & Hfds & Hfs & Hinp).
pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
assert (T : forall x v, (mf <= x /\ x + 8 <= mf + 40) \/ (mf + 48 <= x /\ x + 8 <= 2 ^ 64) ->
  val_mem SEGS (rd W2 mem2) x 8 v -> val_mem SEGS (rd Wf memf) x 8 v).
{ intros x v Hx Hv. exact (d5_tr_val _ _ _ _ _ _ _ _ x 8 v HK (d5_prot_st8 _ _ _ _ x Hx G5) Hv). }
rewrite E2, E9, E8, E3, E4.
split; [exact R2|]. split; [exact R9|]. split; [exact R8|]. split; [exact Hmf|]. split; [exact Hmf32|].
split; [exact R3|]. split; [exact R4|].
split; [apply T; [lia | exact V16]|]. split; [apply T; [lia | exact V64]|].
split; [apply T; [lia | exact V192]|]. split; [apply T; [lia | exact V168]|].
split; [apply T; [lia | exact Vra]|]. split; [apply T; [lia | exact Vs0]|].
split; [apply T; [lia | exact V24]|]. split; [apply T; [lia | exact V32]|].
split; [apply T; [lia | exact V40]|]. split; [apply T; [lia | exact V48]|].
split; [apply T; [lia | exact V56]|]. split; [apply T; [lia | exact V64']|].
split; [apply T; [lia | exact V72]|]. split; [apply T; [lia | exact V80]|].
split; [apply T; [lia | exact V88]|]. split; [apply T; [lia | exact V96]|].
split; [apply T; [lia | exact V104]|].
split.
{ apply (d5_tr_val _ _ _ _ _ _ _ _ _ 8 _ HK); [|exact Vfl].
  intros kk Hkk. apply (d5_prot_fr _ _ _ _ HG); cbn in Hkk; lia. }
split; [exact Hpre|].
split; [intros fd; rewrite Fd; reflexivity|]. split; [exact Fs|].
destruct (d5_pre g Hpre) as (_ & _ & Hcase & Hlen & _ & _).
destruct Hcase as [(Hn0 & _) | (Hn & Hinb)].
- unfold bytes_at8. destruct (e_pl g) as [|b0 l0] eqn:El; [apply garr8_nil|]. cbn [length] in Hlen. lia.
- apply (d5_tr_garr8 _ _ _ _ _ _ _ _ _ _ HK); [|exact Hinp].
  intros x Hx. rewrite length_map, <- Hlen in Hx. apply (d5_prot_bl _ _ _ _ (e_p g) (e_n g) x (Hbl _ _ Hinb)).
  unfold req_size. destruct (Z.eqb_spec (e_n g) 0); lia.
Qed.
Lemma d5_body : forall g pos mf i pl ly2 S2 W2 regs2 mem2 lyf Sf Wf regsf memf bl,
  P_body B g pos mf i pl ly2 S2 W2 regs2 mem2 ->
  d5_keep mf (SFa g pos) bl (d5_ex (SFa g pos)) W2 mem2 Wf memf -> d5_geo mf (SFa g pos) bl ->
  In (pl, SlotModel.rec_k (e_pl g) i) bl ->
  getr regsf 22 = getr regs2 22 -> getr regsf 27 = getr regs2 27 ->
  Permutation (ablocks B lyf Sf) (ablocks B ly2 S2) ->
  P_body B g pos mf i pl lyf Sf Wf regsf memf.
Proof.
intros g pos mf i pl ly2 S2 W2 regs2 mem2 lyf Sf Wf regsf memf bl HPB HK HG Hplb E22 E27 Hperm.
destruct HPB as (Hi & (Hhb1 & Hhb2) & Hpl & (Hidb & Hidz & Hidk) & V96 & Hfix & Hbef & Hag & Hmid & V112 & V120 & V128
  & R22 & R27 & Hcur).
pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
assert (T : forall x v, (mf <= x /\ x + 8 <= mf + 40) \/ (mf + 48 <= x /\ x + 8 <= 2 ^ 64) ->
  val_mem SEGS (rd W2 mem2) x 8 v -> val_mem SEGS (rd Wf memf) x 8 v).
{ intros x v Hx Hv. exact (d5_tr_val _ _ _ _ _ _ _ _ x 8 v HK (d5_prot_st8 _ _ _ _ x Hx G5) Hv). }
assert (SH : forall j, 0 <= j < 128 -> j <> 24 -> d5_prot mf (SFa g pos) bl (d5_ex (SFa g pos)) (shadow_addr (SFa g pos) + j))
  by (intros j Hj Hj24; exact (d5_prot_fsh _ _ _ j HG Hj Hj24)).
pose proof (SlotModel.rec_id_length (e_pl g) (S i)) as Lid. unfold RcIdentModel.ID_SIZE in Lid.
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Lpl. pose proof (SlotModel.rec_k_range (e_pl g) i) as Kr.
unfold P_body. split; [exact Hi|].
split; [split; [exact (Permutation_trans Hperm Hhb1) | exact Hhb2]|].
split.
{ apply (d5_tr_garr8 _ _ _ _ _ _ _ _ _ _ HK); [|exact Hpl].
  intros x Hx. rewrite length_map, Lpl in Hx. apply (d5_prot_bl _ _ _ _ pl _ x Hplb).
  unfold req_size. destruct (Z.eqb_spec (SlotModel.rec_k (e_pl g) i) 0); lia. }
split.
{ unfold id_at, sh_zero, sh_blk, V_id, N_id. split; [|split].
  - apply (d5_tr_garr8 _ _ _ _ _ _ _ _ _ _ HK); [|exact Hidb].
    intros x Hx. unfold m_id in Hx. rewrite length_map, Lid in Hx. apply (d5_prot_fr _ _ _ _ HG); lia.
  - apply (d5_tr_zero _ _ _ _ _ _ _ _ _ _ HK); [|exact Hidz].
    intros j Hj. rewrite (d5_sh_off (SFa g pos) 352 G3) by reflexivity. change (352 / 8) with 44.
    change (38 / 8) with 4 in Hj. rewrite <- Z.add_assoc. apply SH; lia.
  - apply (d5_tr_blk _ _ _ _ _ _ _ _ _ _ HK); [|exact Hidk].
    intros j Hj. rewrite (d5_sh_off (SFa g pos) 352 G3) by reflexivity. change (352 / 8) with 44.
    change ((38 + 7) / 8) with 5 in Hj. rewrite <- Z.add_assoc. apply SH; lia. }
unfold mf_fixed, mf_before, mf_again, mf_id in *.
destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
split; [apply T; [lia | exact V96]|].
split.
{ split; [apply T; [lia | exact F32]|]. split; [apply T; [lia | exact F48]|].
  split; [apply T; [lia | exact F56]|]. split; [apply T; [lia | exact F72]|].
  split; [apply T; [lia | exact F80]|]. split; [apply T; [lia | exact F88]|].
  split; [apply T; [lia | exact F104]|]. split; [apply T; [lia | exact F136]|].
  split; [apply T; [lia | exact F144] | apply T; [lia | exact F160]]. }
split; [apply T; [lia | exact Hbef]|]. split; [apply T; [lia | exact Hag]|]. split; [apply T; [lia | exact Hmid]|].
split; [apply T; [lia | exact V112]|]. split; [apply T; [lia | exact V120]|]. split; [apply T; [lia | exact V128]|].
split; [rewrite E22; exact R22|]. split; [rewrite E27; exact R27 | exact Hcur].
Qed.
Lemma d5_hwb_len : forall inp i, (length (SlotModel.rec_hwb inp i) <= 8)%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb. induction i as [|i IH]; cbn [SlotModel.rec_hw]; [cbn; lia|].
destruct (_ && _); [rewrite length_firstn; lia | exact IH].
Qed.
Lemma d5_hw : forall g pos mf i W2 mem2 Wf memf bl,
  hw_live g pos mf i W2 mem2 ->
  d5_keep mf (SFa g pos) bl (d5_ex (SFa g pos)) W2 mem2 Wf memf -> d5_geo mf (SFa g pos) bl ->
  SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_FIRMWARE ->
  hw_live g pos mf (S i) Wf memf.
Proof.
intros g pos mf i W2 mem2 Wf memf bl ((Hb & Hz & Hk) & V432 & V24) HK HG Ha.
pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
assert (Eb : m_hwb g (S i) = m_hwb g i) by (unfold m_hwb, SlotModel.rec_hwb; rewrite d5_rec_hw_keep by exact Ha; reflexivity).
assert (Eh : m_have g (S i) = m_have g i) by (unfold m_have, SlotModel.rec_have; rewrite d5_rec_hw_keep by exact Ha; reflexivity).
assert (SH : forall j, 0 <= j < 128 -> j <> 24 -> d5_prot mf (SFa g pos) bl (d5_ex (SFa g pos)) (shadow_addr (SFa g pos) + j))
  by (intros j Hj Hj24; exact (d5_prot_fsh _ _ _ j HG Hj Hj24)).
pose proof (d5_hwb_len (e_pl g) i) as Lb.
unfold hw_live, hw_mem, sh_zero, sh_blk, V_hw, N_hw in *. rewrite Eb, Eh.
split; [split; [|split]|split].
- apply (d5_tr_garr8 _ _ _ _ _ _ _ _ _ _ HK); [|exact Hb].
  intros x Hx. unfold m_hwb in Hx. rewrite length_map in Hx. apply (d5_prot_fr _ _ _ _ HG); lia.
- apply (d5_tr_zero _ _ _ _ _ _ _ _ _ _ HK); [|exact Hz].
  intros j Hj. rewrite (d5_sh_off (SFa g pos) 432 G3) by reflexivity. change (432 / 8) with 54.
  change (12 / 8) with 1 in Hj. rewrite <- Z.add_assoc. apply SH; lia.
- apply (d5_tr_blk _ _ _ _ _ _ _ _ _ _ HK); [|exact Hk].
  intros j Hj. rewrite (d5_sh_off (SFa g pos) 432 G3) by reflexivity. change (432 / 8) with 54.
  change ((12 + 7) / 8) with 2 in Hj. rewrite <- Z.add_assoc. apply SH; lia.
- apply (d5_tr_val _ _ _ _ _ _ _ _ _ 4 _ HK); [|exact V432].
  intros kk Hkk. apply (d5_prot_fr _ _ _ _ HG); cbn in Hkk; lia.
- exact (d5_tr_val _ _ _ _ _ _ _ _ (mf + 24) 8 _ HK
    (d5_prot_st8 mf (SFa g pos) bl (d5_ex (SFa g pos)) (mf + 24) ltac:(lia) G5) V24).
Qed.

(* ---- the write rights of the runs' windows ----------------------------------------------------------------- *)
Lemma d5_awr_mf : forall g mf bl0 blc ly own a, e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf + 40 <= a < mf + 48 ->
  awr_byte LLVMF_STK (e_sp0 g) [] bl0 blc ly own a.
Proof. intros g mf bl0 blc ly own a Hmf Ha. left. unfold STK_LLVMF, ASTACK in HSTK. lia. Qed.
Lemma d5_awr_sh : forall g pos bl0 blc ly a, a = shadow_addr (frame_addr ly 4 pos) + 24 ->
  awr_byte LLVMF_STK (e_sp0 g) [] bl0 blc ly [(4, pos)] a.
Proof.
intros g pos bl0 blc ly a Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
right. unfold in_zr. cbn [fst snd]. rewrite d5_fs4. change (1024 / 8) with 128. lia.
Qed.
(* The geometry of the segment's start state. *)
Lemma d5_geo_of : forall ly S (W : world SEGS) mem md pos mf sf,
  AR SEGS B ly S W mem md -> In (4, pos) (frames S) -> frame_addr ly 4 pos = sf ->
  alloc_ceiling + 8192 <= mf -> mf <= 2 ^ 47 ->
  d5_geo mf sf (ablocks B ly S).
Proof.
intros ly S W mem md pos mf sf HAR Hin Hfa Hmf1 Hmf2.
destruct (d5_frame ly S W mem md pos sf HAR Hin Hfa) as (Hf1 & Hf2 & Hf64 & Hfapp & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsh : shadow_addr sf <= SHADOW_OFF + 17592184995840).
{ unfold shadow_addr. assert (sf / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
  change (140737479966720 / 8) with 17592184995840 in *. lia. }
unfold d5_geo. split; [exact Hf1|]. split; [lia|]. split; [exact Hf64|]. split; [lia|]. split; [lia|].
split; [unfold in_app in Hfapp; unfold ASAN_CEIL in Hfapp; lia|]. split; [unfold SHADOW_OFF in Hsh; lia|].
intros b n Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & H4096 & Hcl & Happ & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md b n 4 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hfa, d5_fs4 in Hd.
unfold in_app, ASAN_CEIL in Happ. lia.
Qed.
(* A byte the run may have written lies in one of its regions' windows. *)
Ltac d5_wr H :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  destruct H as (r & Hr & Ha); vm_compute in Hr;
  repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb] in Ha | ]);
  try contradiction.
(* The n-th region of a state's symbolic memory. *)
Ltac d5_reg HS n HR :=
  let HRok := fresh "HRok" in pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HRok & _);
  lazymatch type of HRok with Forall (YP09.region_ok _ ?Ek ?mx) ?rs =>
    let rs' := eval vm_compute in rs in
    let r := eval vm_compute in (nth n rs' d5_rsh) in
    assert (HR : YP09.region_ok SEGS Ek mx r)
      by (apply (proj1 (Forall_forall _ _) HRok); change rs with rs'; cbn [In]; repeat (first [left; reflexivity | right]))
  end; clear HRok.

(* ---- the segment ------------------------------------------------------------------------------------------- *)
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

Theorem seg_D5 : seg_D5_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold seg_D5_stmt. intros g pos mf i pl W2 c2 HC.
unfold inv_caseF, acut in HC.
destruct HC as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo & Hmok & HEC & HP).
destruct HP as (HPB & HHW & Hrr & Hra & R15 & R23 & R26).
(* the model: the payload's first four bytes are digits, and `again` holds their value *)
destruct (d5_rec_fw (e_pl g) i Hrr Hra) as (K4 & DIG & HB2 & HFW).
pose proof (SlotModel.rec_k_range (e_pl g) i) as KR.
pose proof (SlotModel.rec_pl_length (e_pl g) i) as PLL.
pose proof (DIG 0%nat ltac:(lia)) as D0. pose proof (DIG 1%nat ltac:(lia)) as D1.
pose proof (DIG 2%nat ltac:(lia)) as D2. pose proof (DIG 3%nat ltac:(lia)) as D3. clear DIG.
unfold RcIdentModel.fw_value in HFW. unfold m_id in R23, R26. rewrite HB2 in R23. rewrite HFW in R26.
set (rk := SlotModel.rec_k (e_pl g) i) in *.
set (p0 := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0)) in *.
set (p1 := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1)) in *.
set (p2 := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2)) in *.
set (p3 := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)) in *.
(* the cut's facts the runs read *)
destruct (d5_jr g pos ly2 S2 W2 mem2 md2 _ HJ)
  as (HAR & Hfrs & Hin & Hfa & Htop & Hsp0al & Hsp0lo & Hsp0hi & Hsp0top & Hpres & F1).
set (sf := SFa g pos) in *. assert (Hsfe : SFa g pos = sf) by reflexivity.
destruct (d5_frame ly2 S2 W2 mem2 md2 pos sf HAR Hin Hfa) as (Hf1 & Hf2 & Hf64 & Hfapp & Hfb & Hfs).
pose proof HEC as (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & _).
pose proof HPB as (Hi & Hhb & Hplb & _ & _ & Hfix & _ & _ & _ & _ & _ & _ & R22 & R27 & _).
pose proof Hfix as (_ & _ & _ & _ & _ & _ & _ & _ & V144 & V160). unfold V_s in V144.
assert (Hplin : In (pl, rk) (ablocks B ly2 S2))
  by (destruct Hhb as [Hperm _]; apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pl rk HAR Hplin) as (Hpl16 & Hpl4096 & Hplc & Hplapp & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_LLVMF = 16736) by reflexivity.
assert (Hrq : req_size rk = rk) by (unfold req_size; destruct (Z.eqb_spec rk 0); lia).
rewrite Hrq in Hplc, Hplapp.
assert (B0 : val_mem SEGS (rd W2 mem2) (pl + 0) 1 p0).
{ destruct (Hplb 0%nat ltac:(rewrite length_map; lia)) as (X & _). rewrite d5_nth_map in X. exact X. }
assert (B1 : val_mem SEGS (rd W2 mem2) (pl + 1) 1 p1).
{ destruct (Hplb 1%nat ltac:(rewrite length_map; lia)) as (X & _). rewrite d5_nth_map in X. exact X. }
assert (B2 : val_mem SEGS (rd W2 mem2) (pl + 2) 1 p2).
{ destruct (Hplb 2%nat ltac:(rewrite length_map; lia)) as (X & _). rewrite d5_nth_map in X. exact X. }
assert (B3 : val_mem SEGS (rd W2 mem2) (pl + 3) 1 p3).
{ destruct (Hplb 3%nat ltac:(rewrite length_map; lia)) as (X & _). rewrite d5_nth_map in X. exact X. }
assert (Hmfb : 2 ^ 46 <= mf <= 2 ^ 47 /\ alloc_ceiling + 8192 <= mf).
{ unfold STK_LLVMF, ASTACK in HSTK. clear - Hmf Hsp0lo Hsp0hi HSTK C1. lia. }
destruct (d5_entryA W2 regs2 mem2 mf sf pl rk (p0 * 1000 + p1 * 100 + p2 * 10 + p3) p0 p1 p2 p3
  R2 R9 R15 R22 R23 R26 R27) as (HS & SHOK);
  [ lia | exact Hmf32 | lia | lia | lia | apply d5_m64_8; exact Hf64 | lia | lia | lia | lia | lia | lia | lia
  | reflexivity | intros q Hq; apply Hpres; lia | exact V144 | exact V160 | exact B0 | exact B1 | exact B2 | exact B3
  | exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ pl rk pl 4 HAR Hplin ltac:(lia) ltac:(rewrite Hrq; lia))
  | unfold in_app in Hplapp; lia |].
remember (d5_E regs2 sf p0 p1 p2 p3) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold d5_E; apply Eimg_env).
assert (ER : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn Hr; rewrite HE; unfold d5_E; exact (d5_E_reg regs2 _ n r Hn Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (sf + 192)) by (rewrite HE; exact (d5_E_extra regs2 sf p0 p1 p2 p3 0 ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (shadow_addr sf)) by (rewrite HE; exact (d5_E_extra regs2 sf p0 p1 p2 p3 1 ltac:(lia))).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite (ER 9%nat 9%bv) by (reflexivity || lia); rewrite R9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pl) by (rewrite (ER 27%nat 27%bv) by (reflexivity || lia); rewrite R27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = sf + 192) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Hshb : 2147451392 <= shadow_addr sf <= 17594332446720).
{ assert (Hd1 : 512 <= sf / 8)
    by (clear - Hf1; replace 512 with (4096 / 8) by reflexivity; apply Z.div_le_mono; lia).
  assert (Hd2 : sf / 8 <= 17592184995840)
    by (clear - Hf2 C1; replace 17592184995840 with (140737479966720 / 8) by reflexivity;
        apply Z.div_le_mono; lia).
  unfold shadow_addr, SHADOW_OFF. remember (sf / 8) as q eqn:Hq.
  try (rewrite <- Hq in Hd1, Hd2). clear - Hd1 Hd2. lia. }
assert (Hplsep : pl + 4 <= 2147446784 \/ 17594333495296 <= pl)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hplapp; clear - Hplapp K4; lia).
assert (U33 : bv_unsigned (ew E 33) = shadow_addr sf) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = Z_to_bv 64 p0) by (rewrite HE; exact (d5_E_extra regs2 sf p0 p1 p2 p3 2 ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 p1) by (rewrite HE; exact (d5_E_extra regs2 sf p0 p1 p2 p3 3 ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 p2) by (rewrite HE; exact (d5_E_extra regs2 sf p0 p1 p2 p3 4 ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 p3) by (rewrite HE; exact (d5_E_extra regs2 sf p0 p1 p2 p3 5 ltac:(lia))).
assert (U34 : bv_unsigned (ew E 34) = p0) by (rewrite E34; apply unsigned_lit_small; clear - D0; lia).
assert (U35 : bv_unsigned (ew E 35) = p1) by (rewrite E35; apply unsigned_lit_small; clear - D1; lia).
assert (U36 : bv_unsigned (ew E 36) = p2) by (rewrite E36; apply unsigned_lit_small; clear - D2; lia).
assert (U37 : bv_unsigned (ew E 37) = p3) by (rewrite E37; apply unsigned_lit_small; clear - D3; lia).
assert (EW15 : ew E 15 = w64 SHADOW_OFF) by (rewrite (ER 15%nat 15%bv) by (reflexivity || lia); exact R15).
assert (Hsfmf : sf + 1024 <= mf) by (clear - Hf2 Hmfb; lia).
assert (Hsep : sf + 1024 <= 2147450880 \/ 17594333495296 <= sf)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp; clear - Hfapp; lia).
assert (Hshlo : kLowShadowBeg < shadow_addr sf) by (apply d5_sh_lo; clear - Hf1; lia).
clear HE.
unfold cfg_at. change (w64 (BASE + 1840)) with (Z_to_bv 64 (BASE + 1840)).
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 1840)) mem2 (seg_rom SEGS))) in HJ.
(* ---- run A1: +0x730 .. +0xca0, the digit checks and the firmware value ---- *)
paj_run_to_tok RUNTO HS HJ SHOK d5_Bspan 3232.
{ intros a (r & Hr & Ha). unfold d5_ssA in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val d5_rmf d5_rpl] in Ha.
  - rewrite U9 in Ha. apply (d5_awr_mf g mf); [exact Hmf | exact Ha].
  - lia. }
rename ms into ms1. rename HFr into HFr1. rename HJ into HJ1.
set (bl := ablocks B ly2 S2) in *.
assert (HGEO : d5_geo mf sf bl) by (apply (d5_geo_of ly2 S2 W2 mem2 md2 pos); [exact HAR | exact Hin | exact Hfa | lia | lia]).
assert (Hplbl : In (pl, rk) bl) by exact Hplin.
assert (Hplfr : pl + rk <= sf \/ sf + 1024 <= pl).
{ destruct HGEO as (_ & _ & _ & _ & _ & _ & _ & G7). destruct (G7 pl rk Hplbl) as (_ & _ & X & _).
  rewrite Hrq in X. exact X. }
assert (KA1 : d5_keep mf sf bl (fun _ : Z => False) W2 mem2 W2 (ms_mem ms1)).
{ apply (d5_keep_run mf sf bl _ W2 mem2 (ms_mem ms1) E (ss_mem d5_ssA));
  [ exact HGEO | apply d5_sh_lo; lia | intros a [] | exact HFr1 |].
  intros a Hw0. left. d5_wr Hw0; rewrite ?U9 in Ha; lia. }
(* ---- run A2: +0xca0 to the call of reac_identity_fw_str (the shadow byte of `s` is cleared) ---- *)
destruct (d5_state g pos ly2 S2 W2 (ms_mem ms1) _ _ HJ1) as (Hsh1 & Hfrp1 & Hstk1).
assert (EW2 : ew E 2 = w64 mf) by (rewrite (ER 2%nat 2%bv) by (reflexivity || lia); exact R2).
assert (EW9 : ew E 9 = w64 mf) by (rewrite (ER 9%nat 9%bv) by (reflexivity || lia); exact R9).
assert (EW26 : ew E 26 = w64 (p0 * 1000 + p1 * 100 + p2 * 10 + p3))
  by (rewrite (ER 26%nat 26%bv) by (reflexivity || lia); exact R26).
assert (EW27 : ew E 27 = w64 pl) by (rewrite (ER 27%nat 27%bv) by (reflexivity || lia); exact R27).
assert (EW3 : ew E 3 = w64 (as_gp B)) by (rewrite (ER 3%nat 3%bv) by (reflexivity || lia); exact R3).
assert (EW4 : ew E 4 = w64 (as_tp B)) by (rewrite (ER 4%nat 4%bv) by (reflexivity || lia); exact R4).
assert (EW8 : ew E 8 = w64 (e_sp0 g)) by (rewrite (ER 8%nat 8%bv) by (reflexivity || lia); exact R8).
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?Sx _ =>
  assert (X9 : ew Ex 9 = ew E 9) by (cbn [ew ewset Nat.eqb]; reflexivity);
  assert (X27 : ew Ex 27 = ew E 27) by (cbn [ew ewset Nat.eqb]; reflexivity);
  assert (X33 : ew Ex 33 = ew E 33) by (cbn [ew ewset Nat.eqb]; reflexivity);
  assert (HRSH : region_ok SEGS Ex (rd W2 (ms_mem ms1)) d5_rsh) by
    (apply (d5_rsh_ok Ex W2 (ms_mem ms1) sf); [rewrite X33; exact U33 | lia | lia | exact Hsh1]);
  assert (HDJ : all_disjoint Ex d5_rsh (ss_mem Sx)) by
    (cbn [ss_mem];
     cbv [all_disjoint extent_disjoint d5_rsh base_val YP09.r_base YP09.r_lo YP09.r_hi];
     rewrite X9, X27, X33, U9, U27, U33; unfold SHADOW_OFF in Hshb;
     repeat match goal with |- _ /\ _ => split end; try exact I; lia);
  pose proof (st_ok_pi_add_region Ex Sx _ d5_rsh HS ltac:(vm_compute; reflexivity) HRSH HDJ) as HS2
end.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
clear HS HRSH HDJ.
lazymatch type of HS2 with
| st_ok_pi _ _ ?Ex _ _ => assert (SHOK2 : sh_ok SEGS d5_Bx [] Ex (rd W2 (ms_mem ms1))) by apply Forall_nil
end.
(* ---- run A2: the shadow byte of `s` is cleared, up to the call of reac_identity_fw_str ---- *)
paj_run_tok RUN HS2 HJ1 SHOK2 (0, 0).
{ intros a Hw0. d5_wr Hw0.
  - apply (d5_awr_sh g pos). rewrite Hfa. rewrite U33 in Ha. clear - Ha. lia.
  - apply (d5_awr_mf g mf); [exact Hmf|]. rewrite U9 in Ha. clear - Ha. lia.
  - clear - Ha. lia. }
rename ms into ms2, HJ1 into HJ2, HFr into HFr2, HS2 into HSa.
assert (KA2 : d5_keep mf sf bl (fun a => a = shadow_addr sf + 24) W2 (ms_mem ms1) W2 (ms_mem ms2)).
{ eapply (d5_keep_run mf sf bl _ W2 (ms_mem ms1) (ms_mem ms2));
  [ exact HGEO | apply d5_sh_lo; clear - Hf1; lia | intros a ->; right; clear - Hshb; lia | exact HFr2 |].
  intros a Hw0. d5_wr Hw0; [right; rewrite U33 in Ha; clear - Ha; lia | left; rewrite U9 in Ha; clear - Ha; lia
  | clear - Ha; lia]. }
(* the shadow byte of `s` now reads 0, which the call needs for its eight bytes *)
assert (Hsh2 : aview SEGS (w_H W2) (ms_mem ms2) (shadow_addr sf + 24) = Some 0).
{ d5_reg HSa 0%nat HR0.
  pose proof (d5_region_byte _ (w_H W2) (ms_mem ms2) 33 24 25 24 25 _ 24 (SLit 0) 0 HR0
    ltac:(cbn [In]; tauto) ltac:(vm_compute; reflexivity)) as X.
  cbn [base_val ew ewset Nat.eqb] in X. rewrite U33 in X. exact X. }
(* ---- the call of reac_identity_fw_str (0x8142c) ---- *)
pmkst HSa. rewrite (PSIG IB_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
prreg HSa (1%bv : bv 5) Rra. prreg HSa (2%bv : bv 5) Rsp. prreg HSa (10%bv : bv 5) Ra0.
prreg HSa (11%bv : bv 5) Ra1. prreg HSa (12%bv : bv 5) Ra2.
rewrite EW2 in Rsp. rewrite EW26 in Ra0. rewrite E32 in Ra1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS (BASE + AF_reac_identity_fw_str) rg mm mdx) Q) end.
eapply (d5_call_fw g pos ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) _ _ mf (p0 * 1000 + p1 * 100 + p2 * 10 + p3));
  [ exact HJ2 | exact Rra | exact Rsp | exact Ra0 | exact Ra1 | exact Ra2
  | clear - D0 D1 D2 D3; lia | exact Hmf32 | exact Hmf | exact Hsh2 |].
intros Wc cc HPOST.
unfold reac_identity_fw_str.treac_identity_fw_str_post in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & Hperm3 & HPW).
assert (Hfww : reac_identity_fw_str.fw_writes (SFa g pos + 192) 8 = true).
{ rewrite Hsfe. unfold reac_identity_fw_str.fw_writes.
  destruct (Z.eqb_spec (sf + 192) 0) as [Heq | Hne]; [exfalso; clear - Hf1 Heq; lia | reflexivity]. }
rewrite Hfww in HPW. destruct HPW as (Ha03 & Hgar3 & Htcj3).
rewrite (d5_fw_L (p0 * 1000 + p1 * 100 + p2 * 10 + p3) ltac:(clear - D0 D1 D2 D3; lia)) in Ha03.
rewrite (d5_fw_bytes p0 p1 p2 p3 D0 D1 D2 D3) in Hgar3.
rewrite (reac_identity_fw_str.fw_n_short (p0 * 1000 + p1 * 100 + p2 * 10 + p3)
  ltac:(clear - D0 D1 D2 D3; lia)) in Htcj3.
assert (Hsp2 : spZ (ms_regs ms2) = mf)
  by (unfold spZ; rewrite Rsp; apply unsigned_lit_small; clear - Hmfb; lia).
rewrite Hsp2 in Htcj3. rewrite Hsfe in Htcj3, Hgar3.
assert (KFW : d5_keep mf sf bl (fun a => sf + 192 <= a < sf + 198) W2 (ms_mem ms2) Wc mem3).
{ apply (d5_keep_fw mf sf bl _ ly2 S2 W2 (ms_mem ms2) Wc mem3 pos reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK);
  [ exact HGEO | clear - Hmfb; lia | exact Htcj3 | intros b n Hb; exact Hb | exact Hin | exact Hfa
  | intros a Ha; exact Ha ]. }
(* ---- back in the entry: pin a0 = 5, add the region of `s`, run to the call of check_str ---- *)
jafter_call_keep_pi HSa 41%nat regs3 (mrestrict (w_H Wc) mem3) HP3 [1; 2]%nat HS3.
match type of HS3 with ?tq -> _ =>
  assert (HRK : tq) by
    (cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; split;
     cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb];
     intros a Ha;
     [ apply (mbyte_of_aview SEGS); destruct Htcj3 as (T1 & _); apply T1;
       [rewrite U9 in Ha; clear - Ha Hmfb C1; lia | rewrite U9 in Ha; clear - Ha; lia
       | rewrite U9 in Ha; clear - Ha Hmfb Hf2 C1; cbv beta; lia]
     | intros _; apply (apresent_writable SEGS);
       destruct (d5_state g pos ly3 S3 Wc mem3 md3 _ HJ3) as (_ & _ & Hst3); apply Hst3;
       rewrite U9 in Ha; clear - Ha Hmf HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia
     | apply (mbyte_of_aview SEGS); destruct Htcj3 as (_ & T2 & _);
       rewrite U27 in Ha; replace a with (pl + (a - pl)) by ring;
       apply (T2 pl rk (a - pl) Hplin);
       [rewrite Hrq; clear - Ha K4; lia | cbv beta; clear - Ha Hplfr K4; lia]
     | rewrite U27 in Ha; clear - Ha; lia]);
  specialize (HS3 HRK); clear HRK
end.
rewrite <- restrict_mkst_fx in HS3.
rewrite Rra.
(* a0 = L v = 5: pinned, so that s10 (= a0, 0x81430) decides the check at 0x81444 after check_str *)
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 5 HS3 Ha03 eq_refl) as HSB.
clear HS3.
lazymatch type of HSB with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HSB end.
lazymatch type of HSB with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEIb : img_env VAL A_LIM E2)
    by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
(* the region of `s`: the six bytes reac_identity_fw_str wrote *)
lazymatch type of HSB with
| st_ok_pi _ _ ?Ex ?Sx _ =>
  assert (Y9 : ew Ex 9 = ew E 9) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Y27 : ew Ex 27 = ew E 27) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Y32 : ew Ex 32 = ew E 32) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Y34 : ew Ex 34 = ew E 34) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Y35 : ew Ex 35 = ew E 35) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Y36 : ew Ex 36 = ew E 36) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Y37 : ew Ex 37 = ew E 37) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (HRS : region_ok SEGS Ex (rd Wc mem3) d5_rs) by
    (apply (d5_rs_ok Ex Wc mem3 sf p0 p1 p2 p3);
     [ rewrite Y32; exact U32 | rewrite Y34; exact U34 | rewrite Y35; exact U35 | rewrite Y36; exact U36
     | rewrite Y37; exact U37 | exact D0 | exact D1 | exact D2 | exact D3 | clear - Hf1; lia
     | clear - Hsfmf Hmfb; lia | exact Hgar3 ]);
  assert (HDJ : all_disjoint Ex d5_rs (ss_mem Sx)) by
    (cbn [ss_mem];
     cbv [all_disjoint extent_disjoint d5_rs base_val YP09.r_base YP09.r_lo YP09.r_hi];
     rewrite ?Y9, ?Y27, ?Y32, ?U9, ?U27, ?U32;
     repeat match goal with |- _ /\ _ => split end; try exact I; clear - Hsfmf Hplfr K4; lia);
  pose proof (st_ok_pi_add_region Ex Sx _ d5_rs HSB ltac:(vm_compute; reflexivity) HRS HDJ) as HSB2
end.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSB2.
clear HSB HRS HDJ.
lazymatch type of HSB2 with
| st_ok_pi _ _ ?Ex _ _ => assert (SHOKB : sh_ok SEGS d5_Bx [] Ex (rd Wc mem3)) by apply Forall_nil
end.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (BASE + 3260)) mem3 (seg_rom SEGS))) in HJ3.
(* ---- run B: +0xcbc to the call of check_str (s10 := a0, a1 := &s, a2 := 8) ---- *)
paj_run_tok RUN HSB2 HJ3 SHOKB (0, 0).
{ intros a Hw0. d5_wr Hw0; rewrite ?U9 in Ha;
  first [ clear - Ha; lia | apply (d5_awr_mf g mf); [exact Hmf | clear - Ha; lia] ]. }
rename ms into msB, HJ3 into HJB, HFr into HFrB, HSB2 into HSb.
assert (KB : d5_keep mf sf bl (fun _ : Z => False) Wc mem3 Wc (ms_mem msB)).
{ eapply (d5_keep_run mf sf bl _ Wc mem3 (ms_mem msB));
  [ exact HGEO | exact Hshlo | intros a [] | exact HFrB |].
  intros a Hw0. left. d5_wr Hw0; rewrite ?U9 in Ha; clear - Ha; lia. }
assert (K2B : d5_keep mf sf bl (d5_ex sf) W2 mem2 Wc (ms_mem msB)).
{ eapply d5_keep_trans; [d5_km KA1|]. eapply d5_keep_trans; [d5_km KA2|].
  eapply d5_keep_trans; [d5_km KFW|]. d5_km KB. }
assert (HshB : aview SEGS (w_H Wc) (ms_mem msB) (shadow_addr sf + 24) = Some 0).
{ rewrite (KB _ (d5_prot_fsh0 mf sf bl (fun _ : Z => False) 24 ltac:(lia) (fun X => X))).
  assert (Hn : ~ (sf + 192 <= shadow_addr sf + 24 < sf + 198)) by (intros X; clear - X Hsep Hshb; lia).
  rewrite (KFW _ (d5_prot_fsh0 mf sf bl (fun a => sf + 192 <= a < sf + 198) 24 ltac:(lia) Hn)).
  exact Hsh2. }
assert (HgarB : garr8 SEGS (rd Wc (ms_mem msB)) (sf + 192) [48 + p0; 46; 48 + p1; 48 + p2; 48 + p3; 0]).
{ apply (d5_tr_garr8 _ _ _ _ _ _ _ _ _ _ KB); [|exact Hgar3].
  intros x Hx. apply d5_prot_fr0; [cbn [length] in Hx; clear - Hx; lia | intros []]. }
pose proof HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vra & Vs0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & Hpre & _).
assert (P8 : (mf <= e_sp0 g - 8 /\ e_sp0 g - 8 + 8 <= mf + 40) \/ (mf + 48 <= e_sp0 g - 8 /\ e_sp0 g - 8 + 8 <= 2 ^ 64))
  by (right; clear - Hmf Hsp0hi; lia).
assert (P16 : (mf <= e_sp0 g - 16 /\ e_sp0 g - 16 + 8 <= mf + 40) \/ (mf + 48 <= e_sp0 g - 16 /\ e_sp0 g - 16 + 8 <= 2 ^ 64))
  by (right; clear - Hmf Hsp0hi; lia).
assert (Hmf47 : mf <= 2 ^ 47) by (clear - Hmfb; lia).
assert (Vra2 : val_mem SEGS (rd Wc (ms_mem msB)) (e_sp0 g - 8) 8 RA_LLVMF)
  by exact (d5_tr_val _ _ _ _ _ _ _ _ (e_sp0 g - 8) 8 _ K2B
    (d5_prot_st8 mf sf bl (d5_ex sf) (e_sp0 g - 8) P8 Hmf47) Vra).
assert (Vs02 : val_mem SEGS (rd Wc (ms_mem msB)) (e_sp0 g - 16) 8 (s0Z (e_regs g)))
  by exact (d5_tr_val _ _ _ _ _ _ _ _ (e_sp0 g - 16) 8 _ K2B
    (d5_prot_st8 mf sf bl (d5_ex sf) (e_sp0 g - 16) P16 Hmf47) Vs0).
(* ---- the call of check_str (0x8143c): check_str (5, &s, 8) ---- *)
pmkst HSb. rewrite (PSIG IB_check_str AF_check_str eq_refl).
prreg HSb (1%bv : bv 5) Rra2. prreg HSb (2%bv : bv 5) Rsp2. prreg HSb (3%bv : bv 5) Rgp2.
prreg HSb (4%bv : bv 5) Rtp2. prreg HSb (8%bv : bv 5) Rs02. prreg HSb (10%bv : bv 5) Ra02.
prreg HSb (11%bv : bv 5) Ra12. prreg HSb (12%bv : bv 5) Ra22.
rewrite EW2 in Rsp2. rewrite EW3 in Rgp2. rewrite EW4 in Rtp2. rewrite EW8 in Rs02. rewrite E32 in Ra12.
destruct (d5_jr g pos ly3 S3 Wc _ _ _ HJB) as (_ & Hfrs3' & Hin3 & Hfa3 & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  eapply (d5_call_chk g pos ly3 S3 Wc (mkst rg (Z_to_bv 64 (BASE + AF_check_str)) mm (seg_rom SEGS)) mdx _ mf
    p0 p1 p2 p3 Q eq_refl HJB Hpre Rra2 Rsp2 Rgp2 Rtp2 Rs02 Ra02 Ra12 Ra22 Hmf32 Hmf Vra2 Vs02 D0 D1 D2 D3 HgarB HshB)
end.
intros W' c' (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJs & HP4 & -> & -> & ->).
rewrite Z.add_0_r in HJ4.
assert (KC : d5_keep mf sf bl (fun _ : Z => False) Wc (ms_mem msB) Wc mem4).
{ refine (d5_keep_chk mf sf bl _ check_str.CHECK_STR_STK ly3 S3 Wc (ms_mem msB) _ ly3 S3 Wc mem4 md4 0 pos
    HGEO _ HJs _ Hin3 Hfa3).
  - clear - Hmfb; lia.
  - intros b n Hb. assert (X : In (b, n) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym Hperm3) Hb).
    split; exact X. }
jafter_call_keep_pi HSb 57%nat regs4 (mrestrict (w_H Wc) mem4) HP4 [0; 1; 2]%nat HS5.
match type of HS5 with ?tq -> _ =>
  assert (HRK : tq) by
    (cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; split;
     cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb];
     intros a Ha;
     [ apply (mbyte_of_aview SEGS); rewrite U32 in Ha; apply KC; apply d5_prot_fr0;
       [clear - Ha; lia | intros []]
     | rewrite U32 in Ha; clear - Ha; lia
     | apply (mbyte_of_aview SEGS); rewrite U9 in Ha;
       apply (d5_chk_st _ _ _ _ _ _ _ _ _ _ _ _ _ HJs); [clear - Hmfb; lia | clear - Ha Hmfb; lia]
     | intros _; apply (apresent_writable SEGS);
       destruct (d5_state g pos ly3 S3 Wc mem4 md4 _ HJ4) as (_ & _ & Hst4); apply Hst4;
       rewrite U9 in Ha; clear - Ha Hmf HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia
     | apply (mbyte_of_aview SEGS); rewrite U27 in Ha; apply KC;
       apply (d5_prot_bl _ _ _ _ pl rk a Hplbl); rewrite Hrq; clear - Ha K4; lia
     | rewrite U27 in Ha; clear - Ha; lia ]);
  specialize (HS5 HRK); clear HRK
end.
rewrite <- restrict_mkst_fx in HS5.
lazymatch type of HS5 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS5 end.
lazymatch type of HS5 with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEIc : img_env VAL A_LIM E2)
    by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
destruct (d5_jr g pos ly3 S3 Wc mem4 md4 _ HJ4) as (HAR4 & _).
assert (Hpl3 : In (pl, rk) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym Hperm3) Hplbl).
lazymatch type of HS5 with st_ok_pi _ _ ?Ex _ _ =>
  assert (SHOKC : sh_ok SEGS d5_Bx d5_SH Ex (rd Wc mem4)) by
    (apply (d5_shok Ex Wc mem4 pl);
     [ cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact EW15
     | cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact EW27
     | clear - Hpl4096; lia | clear - Hplc C1 K4; lia
     | unfold kLowShadowBeg, kHighMemBeg; clear - Hplsep; lia
     | exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ pl rk pl 4 HAR4 Hpl3 ltac:(clear - K4; lia)
         ltac:(rewrite Hrq; clear - K4; lia)) ])
end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 (BASE + 3276)) mem4 (seg_rom SEGS))) in HJ4.
(* ---- run C: +0xccc .. +0xdc8, the five byte checks of `s` ---- *)
paj_run_to_tok RUNTO HS5 HJ4 SHOKC d5_Bspan 3528.
{ intros a Hw0. d5_wr Hw0; rewrite ?U9 in Ha;
  first [ clear - Ha; lia | apply (d5_awr_mf g mf); [exact Hmf | clear - Ha; lia] ]. }
rename ms into msC, HJ4 into HJC, HFr into HFrC, HS5 into HSc.
assert (KCC : d5_keep mf sf bl (fun _ : Z => False) Wc mem4 Wc (ms_mem msC)).
{ eapply (d5_keep_run mf sf bl _ Wc mem4 (ms_mem msC));
  [ exact HGEO | exact Hshlo | intros a [] | exact HFrC |].
  intros a Hw0. left. d5_wr Hw0; rewrite ?U9 in Ha; clear - Ha; lia. }
(* ---- run D: +0xdc8 .. +0xe24, `s` poisoned again (0xf8 into its shadow byte), the jump to the join ---- *)
destruct (d5_state g pos ly3 S3 Wc _ _ _ HJC) as (HshC & _ & _).
lazymatch type of HSc with
| st_ok_pi _ _ ?Ex ?Sx _ =>
  assert (Z9 : ew Ex 9 = ew E 9) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Z27 : ew Ex 27 = ew E 27) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Z32 : ew Ex 32 = ew E 32) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (Z33 : ew Ex 33 = ew E 33) by (cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; reflexivity);
  assert (HRSH : region_ok SEGS Ex (rd Wc (ms_mem msC)) d5_rsh) by
    (apply (d5_rsh_ok Ex Wc (ms_mem msC) sf); [rewrite Z33; exact U33 | clear - Hf1; lia | clear - Hf2 C1; lia
     | exact HshC]);
  assert (HDJ : all_disjoint Ex d5_rsh (ss_mem Sx)) by
    (cbn [ss_mem];
     cbv [all_disjoint extent_disjoint d5_rsh base_val YP09.r_base YP09.r_lo YP09.r_hi];
     rewrite ?Z9, ?Z27, ?Z32, ?Z33, ?U9, ?U27, ?U32, ?U33;
     repeat match goal with |- _ /\ _ => split end; try exact I; clear - Hshb Hsep Hmfb Hplsep; lia);
  pose proof (st_ok_pi_add_region Ex Sx _ d5_rsh HSc ltac:(vm_compute; reflexivity) HRSH HDJ) as HSd
end.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSd.
clear HSc HRSH HDJ.
lazymatch type of HSd with
| st_ok_pi _ _ ?Ex _ _ => assert (SHOKD : sh_ok SEGS d5_Bx [] Ex (rd Wc (ms_mem msC))) by apply Forall_nil
end.
paj_run_to_tok RUNTO HSd HJC SHOKD (0, 0) 3620.
{ intros a Hw0. d5_wr Hw0; rewrite ?U9, ?U33 in Ha;
  first [ clear - Ha; lia | apply (d5_awr_mf g mf); [exact Hmf | clear - Ha; lia]
        | apply (d5_awr_sh g pos); rewrite Hfa3, Hsfe; clear - Ha; lia ]. }
rename ms into msD, HJC into HJD, HFr into HFrD, HSd into HSD.
assert (KD : d5_keep mf sf bl (fun a => a = shadow_addr sf + 24) Wc (ms_mem msC) Wc (ms_mem msD)).
{ eapply (d5_keep_run mf sf bl _ Wc (ms_mem msC) (ms_mem msD));
  [ exact HGEO | exact Hshlo | intros a ->; right; clear - Hshb; lia | exact HFrD |].
  intros a Hw0. d5_wr Hw0; rewrite ?U9, ?U33 in Ha;
  first [ right; clear - Ha; lia | left; clear - Ha; lia ]. }
assert (KF : d5_keep mf sf bl (d5_ex sf) W2 mem2 Wc (ms_mem msD)).
{ eapply d5_keep_trans; [exact K2B|]. eapply d5_keep_trans; [d5_km KC|].
  eapply d5_keep_trans; [d5_km KCC|]. d5_km KD. }
(* ---- the cut inv_tail at +0xe24 ---- *)
pmkst HSD.
prreg HSD (2%bv : bv 5) Rf2. prreg HSD (3%bv : bv 5) Rf3. prreg HSD (4%bv : bv 5) Rf4.
prreg HSD (8%bv : bv 5) Rf8. prreg HSD (9%bv : bv 5) Rf9. prreg HSD (22%bv : bv 5) Rf22.
prreg HSD (27%bv : bv 5) Rf27.
assert (F2 : getr (ms_regs msD) 2 = getr regs2 2)
  by (rewrite Rf2; exact (ER 2%nat 2%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl)).
assert (F3 : getr (ms_regs msD) 3 = getr regs2 3)
  by (rewrite Rf3; exact (ER 3%nat 3%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl)).
assert (F4 : getr (ms_regs msD) 4 = getr regs2 4)
  by (rewrite Rf4; exact (ER 4%nat 4%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl)).
assert (F8 : getr (ms_regs msD) 8 = getr regs2 8)
  by (rewrite Rf8; exact (ER 8%nat 8%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl)).
assert (F9 : getr (ms_regs msD) 9 = getr regs2 9)
  by (rewrite Rf9; exact (ER 9%nat 9%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl)).
assert (F22 : getr (ms_regs msD) 22 = getr regs2 22)
  by (rewrite Rf22; exact (ER 22%nat 22%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl)).
assert (F27 : getr (ms_regs msD) 27 = getr regs2 27)
  by (rewrite Rf27; exact (ER 27%nat 27%bv ltac:(apply Nat.ltb_lt; reflexivity) eq_refl)).
apply SRr_ret.
unfold inv_tail, acut. cbv beta.
exists ly3, S3, (ms_regs msD), (ms_mem msD). eexists. split; [reflexivity|].
split; [exact HJD|].
split; [rewrite Hfrs3; exact Hfr|].
split; [exact Hk|].
split.
{ pose proof (mo_le_trans MT MTL _ _ _ _ _ Hmo (HMT0 S2 S3)) as X. rewrite Z.add_0_r in X. exact X. }
split.
{ apply (mo_ok_step MT MTL S2 S3 0); [rewrite Z.add_0_l; exact Hmok | apply HMT0]. }
split.
{ refine (d5_ecommon g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 Wc (ms_regs msD) (ms_mem msD) _ _ bl
    HEC KF HGEO _ F2 F9 F8 F3 F4 HJD).
  intros b n Hb. apply (Permutation_in _ (Permutation_sym (proj1 Hhb))). right. exact Hb. }
split.
- exact (d5_body g pos mf i pl ly2 S2 W2 regs2 mem2 ly3 S3 Wc (ms_regs msD) (ms_mem msD) bl
    HPB KF HGEO Hplbl F22 F27 Hperm3).
- exact (d5_hw g pos mf i W2 mem2 Wc (ms_mem msD) bl HHW KF HGEO Hra).
Qed.
Print Assumptions seg_D5.

Check (seg_D5 : seg_D5_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

End c.

End b.
End a.
