(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 790 of its 852 lines of code are new or changed and 968 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op0: Lemma lc_op0_ok : lc_op0_stmt B MT XL RLO RHI (no kit argument), the segment OP0
   of the image-B walk of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput (lc_op0_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v): from the first instruction of arm 0 (+0x5f4, lc_st_arm cx op 0) to the
   call of receive (+0xc00, lc_st_recv cx op): the inlined fuzz_record (TOps.v fuzz_record_m) and the arguments of
   receive.
   rule 24: no function proved
   proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk, image B)

   What the code does (offsets from 0x812a0, lib/B/Prog/DgnTransportBList.v). At the arm s9 / s7 hold the cursor c
   before the op byte (p + fi_off c, fi_n c), s8 / s11 the cursor after it (p + fi_off c + 1, fi_n c - 1), s6 = 1,
   s10 the shadow base.
     +0x5f4  `beqz s11, +0x9f8`: no byte left (fi_n c = 1): +0x9f8 s7 = 0, a1 = 0, a2 = 0, `j +0xbd8`;
     +0x5f8  a0 = s8 + 1, `bltu s6, a0` (the UBSan cursor test; its `j` to the trap word, 0x818a0, is not taken:
             s8 + 1 > 1), the check of the byte at s8: the shadow byte at (s8 >> 3) + s10, `beqz a0, +0x618`, else
             `j +0x16f4`, the slow path `andi a1, s8, 7; bge a1, a0` (the report 0x82f2c) and `j +0x618`;
     +0x618  `lbu a1, 0(s8)`, s8 = s9 + 2, `bne s7, 2, +0xbb0`: one byte left (fi_n c = 2): s7 = 0, `j +0xa00`, a2 = 0,
             `j +0xbd8`;
     +0xbb0  a2 = s8 + 1, `bgeu s6, a2` (the cursor test 0x81e54, not taken), the checked load of the byte at s8
             (`bnez a2, +0x1754`, the slow path `andi a3, s8, 7; blt a3, a2, +0xbc8; j` to the report 0x82f68),
             +0xbc8 `lbu a2`, s7 -= 3, s8 = s9 + 3, a2 <<= 8;
     +0xbd8  a1 = a2 | a1 (the record's length word), `bltu a1, s7` / `mv a1, s7` (its min with the bytes left),
             a0 = ~s8, `bltu a0, a1` (the UBSan test of the take, 0x81e88: never taken, s8 + a1 < 2 ^ 47), s5 = s8 + a1,
             s11 = s7 - a1, a0 = s8, a2 = 0, a3 = 0; +0xc00 is the call of receive (the cut).
   The three paths are fuzz_record_m's three cases at the cursor after the op byte (0, 1, at least 2 bytes left:
   o0_rv1, o0_rv2, o0_rv3). The runs are the position-abstract runs of lib/B/Prog/TransportGRunB.v paj_run_x /
   paj_run_to_x over the walk's G journal, split at each branch the engine leaves open (DgnTransportBPaLib.v
   psrr_branch_tok):
     case 1  (fi_n c = 1, s11 pinned to 0): the run to the take test, its split (taken: refuted, ~s8 >= 2 ^ 64 - 2 ^ 47
             > 0), the run to the cut;
     run A   (fi_n c >= 2, o0_ssA): from the arm to the shadow test of the first byte. The shadow byte is a read-only
             region at the shadow address of s8 (the alias fact (s8 >> 3) + s10 = atom 32), its value sb (atom 33) the
             input block's shadow (YCbq.v range_addressable_of_block: sb = 0 or s8 mod 8 < sb < 8). The engine decides
             `beqz s11` and the cursor test (s6 = 1 < s8 + 1); `beqz a0` is split: sb = 0 goes to +0x618; sb <> 0 runs
             the slow path to `bge a1, a0`, whose taken side (the report call 0x82f2c) is refuted by s8 mod 8 < sb, and
             its `j` to +0x618. Run A writes no byte and changes a0 / a1 only, so every path reaches +0x618 with the
             arm's other registers; the rest of the walk (o0_cont) starts there:
     case 2  (fi_n c = 2, s7 pinned to 2, the byte at s8): the run to the take test, its split, the run to the cut;
     case 3  (fi_n c >= 3, the bytes at s8 and s9 + 2): the engine decides `bne s7, 2` and the cursor test
             (s6 = 1 < s9 + 3) and follows the second checked load with its shadow entry over the input byte at s9 + 2
             (the slow path's `blt` returns to the load; the report 0x82f68 is not reached); then the split at
             `bltu a1, s7`, on each side the split of the take test (taken: refuted) and the run to the cut.
   The input is a heap block of the cut's blocks (st.v lc_geom lg_in), so its shadow admits both loads. The segment
   writes no byte: the memory at the cut is the arm's, the journal is the run's, and every other fact of lc_lcore
   carries over (o0_lcore_regs). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB YE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model: the record op 0 hands receive                          *)
(* ------------------------------------------------------------------ *)

Lemma o0_at8 : forall D i, 0 <= DSpec.at8 D i < 256.
Proof.
intros D i. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth i D (DSpec.b8 0))) as R.
unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* `slli a2, a2, 8; or a1, a2, a1`: the two bytes of the length word do not overlap. *)
Lemma o0_lor8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (x * 2 ^ 8) y = x * 2 ^ 8 + y.
Proof.
intros x y Hx Hy. symmetry. apply Z.add_nocarry_lor.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec i 8) as [Hl|Hl].
- replace (x * 2 ^ 8) with (Z.shiftl x 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r x (i - 8)) by lia. reflexivity.
- rewrite <- (Z.mod_small y (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia.
  apply andb_false_r.
Qed.

Lemma o0_lor : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor lo (Z.shiftl hi 8) = lo + 256 * hi.
Proof.
intros lo hi Hl Hh. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm, (o0_lor8 hi lo Hh Hl).
change (2 ^ 8) with 256. lia.
Qed.

Lemma o0_u8 : forall D c, TOP.fi_n c <> 0 ->
  TOP.fuzz_u8_m D c = (TOP.FuzzIn (TOP.fi_off c + 1) (TOP.fi_n c - 1), DSpec.at8 D (Z.to_nat (TOP.fi_off c))).
Proof. intros D c Hn. unfold TOP.fuzz_u8_m. destruct (Z.eqb_spec (TOP.fi_n c) 0); [lia | reflexivity]. Qed.

Lemma o0_u8_0 : forall D o, TOP.fuzz_u8_m D (TOP.FuzzIn o 0) = (TOP.FuzzIn o 0, 0).
Proof. intros D o. reflexivity. Qed.

(* The cursor after the op byte. *)
Lemma o0_oc : forall D c, TOP.fi_n c <> 0 -> lc_oc D c = TOP.FuzzIn (TOP.fi_off c + 1) (TOP.fi_n c - 1).
Proof. intros D c Hn. unfold lc_oc. rewrite (o0_u8 D c Hn). reflexivity. Qed.

(* Op 0's record: fuzz_record_m at the cursor after the op byte, by_poll = poll_flags = 0. *)
Lemma o0_rv : forall D c, TOP.fi_n c <> 0 -> lc_opc D c = 0 ->
  lc_recv_vals D c =
  let '(c2, off, n) := TOP.fuzz_record_m D (TOP.FuzzIn (TOP.fi_off c + 1) (TOP.fi_n c - 1)) in mkLrv 0 0 off n c2.
Proof.
intros D c Hn Ho. unfold lc_opc in Ho. unfold lc_recv_vals. rewrite (o0_u8 D c Hn) in Ho |- *.
cbn [snd] in Ho. cbv beta iota zeta. rewrite Ho. reflexivity.
Qed.

(* fuzz_record_m on a cursor of 0, 1 and at least 2 bytes. *)
Lemma o0_rec0 : forall D o, TOP.fuzz_record_m D (TOP.FuzzIn o 0) = (TOP.FuzzIn o 0, o, 0).
Proof.
intros D o. unfold TOP.fuzz_record_m, TOP.fuzz_u16_m. rewrite o0_u8_0. cbv beta iota. rewrite o0_u8_0.
cbv beta iota. unfold TOP.fuzz_take_m. cbn. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma o0_rec1 : forall D o, TOP.fuzz_record_m D (TOP.FuzzIn o 1) = (TOP.FuzzIn (o + 1) 0, o + 1, 0).
Proof.
intros D o. unfold TOP.fuzz_record_m, TOP.fuzz_u16_m. rewrite (o0_u8 D (TOP.FuzzIn o 1)) by (cbn; lia).
cbv beta iota. cbn [TOP.fi_off TOP.fi_n]. replace (1 - 1) with 0 by lia. rewrite o0_u8_0. cbv beta iota.
unfold TOP.fuzz_take_m. cbn [TOP.fi_off TOP.fi_n].
lazymatch goal with |- context [if ?w <? 0 then _ else _] =>
  lazymatch w with ?x mod ?y => pose proof (Z.mod_pos_bound x y ltac:(lia)) as Hw end;
  destruct (Z.ltb_spec w 0) as [Hlt|_]; [lia|] end.
cbv zeta. rewrite Z.add_0_r. reflexivity.
Qed.

(* The record's length word: the byte at o, then the byte at o + 1 above it. *)
Definition o0_w (D : list byte) (o : Z) : Z :=
  DSpec.at8 D (Z.to_nat (o + 1)) + 256 * DSpec.at8 D (Z.to_nat (o + 2)).
Definition o0_len (D : list byte) (o n : Z) : Z := if o0_w D o <? n - 3 then o0_w D o else n - 3.

Lemma o0_rec2 : forall D o n, 2 <= n ->
  TOP.fuzz_record_m D (TOP.FuzzIn o n) =
  (TOP.FuzzIn (o + 2 + o0_len D (o - 1) (n + 1)) (n - 2 - o0_len D (o - 1) (n + 1)), o + 2,
   o0_len D (o - 1) (n + 1)).
Proof.
intros D o n Hn. unfold TOP.fuzz_record_m, TOP.fuzz_u16_m.
rewrite (o0_u8 D (TOP.FuzzIn o n)) by (cbn; lia). cbv beta iota. cbn [TOP.fi_off TOP.fi_n].
rewrite (o0_u8 D (TOP.FuzzIn (o + 1) (n - 1))) by (cbn; lia). cbv beta iota. cbn [TOP.fi_off TOP.fi_n].
pose proof (o0_at8 D (Z.to_nat o)) as R0. pose proof (o0_at8 D (Z.to_nat (o + 1))) as R1.
rewrite (o0_lor _ _ R0 R1).
rewrite (Z.mod_small (DSpec.at8 D (Z.to_nat o) + 256 * DSpec.at8 D (Z.to_nat (o + 1))) (2 ^ 16)) by lia.
unfold TOP.fuzz_take_m, o0_len, o0_w. cbn [TOP.fi_off TOP.fi_n]. cbv zeta.
replace (o - 1 + 1) with o by lia. replace (o - 1 + 2) with (o + 1) by lia. replace (n + 1 - 3) with (n - 2) by lia.
replace (n - 1 - 1) with (n - 2) by lia. replace (o + 1 + 1) with (o + 2) by lia.
reflexivity.
Qed.

(* The three cases of lc_recv_vals at op 0, by the bytes left after the op byte. *)
Lemma o0_rv1 : forall D c, TOP.fi_n c = 1 -> lc_opc D c = 0 ->
  lc_recv_vals D c = mkLrv 0 0 (TOP.fi_off c + 1) 0 (TOP.FuzzIn (TOP.fi_off c + 1) 0).
Proof.
intros D c Hn Ho. rewrite (o0_rv D c ltac:(lia) Ho). rewrite Hn. change (1 - 1) with 0. rewrite o0_rec0.
reflexivity.
Qed.

Lemma o0_rv2 : forall D c, TOP.fi_n c = 2 -> lc_opc D c = 0 ->
  lc_recv_vals D c = mkLrv 0 0 (TOP.fi_off c + 2) 0 (TOP.FuzzIn (TOP.fi_off c + 2) 0).
Proof.
intros D c Hn Ho. rewrite (o0_rv D c ltac:(lia) Ho). rewrite Hn. change (2 - 1) with 1. rewrite o0_rec1.
replace (TOP.fi_off c + 1 + 1) with (TOP.fi_off c + 2) by lia. reflexivity.
Qed.

Lemma o0_rv3 : forall D c, 3 <= TOP.fi_n c -> lc_opc D c = 0 ->
  lc_recv_vals D c =
  mkLrv 0 0 (TOP.fi_off c + 3) (o0_len D (TOP.fi_off c) (TOP.fi_n c))
    (TOP.FuzzIn (TOP.fi_off c + 3 + o0_len D (TOP.fi_off c) (TOP.fi_n c))
                (TOP.fi_n c - 3 - o0_len D (TOP.fi_off c) (TOP.fi_n c))).
Proof.
intros D c Hn Ho. rewrite (o0_rv D c ltac:(lia) Ho).
rewrite (o0_rec2 D (TOP.fi_off c + 1) (TOP.fi_n c - 1)) by lia.
replace (TOP.fi_off c + 1 - 1) with (TOP.fi_off c) by lia. replace (TOP.fi_n c - 1 + 1) with (TOP.fi_n c) by lia.
replace (TOP.fi_off c + 1 + 2) with (TOP.fi_off c + 3) by lia.
replace (TOP.fi_n c - 1 - 2) with (TOP.fi_n c - 3) by lia.
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The seats of the runs                                            *)
(* ------------------------------------------------------------------ *)

(* The arm (lo_arm 0), the rejoin after the first byte's check, and the cut (LO_RECV) as offsets of the listing (its
   base is the entry, AF_LLVMFuzzerTestOneInput = 0); the shadow base s10 is the token engine's Bx. *)
Definition O0_ARM : Z := 0x5f4.
Definition O0_618 : Z := 0x618.
Definition O0_RECV : Z := 0xc00.
Definition o0_Bx : sv := SOff 26 0.
Definition o0_PTR : afact := mkAF 4096 140737479966720 0.
(* Case 1 (fi_n c = 1): no region; s11 is pinned to 0 at the seat. *)
Definition o0_ss1 : sstate := mkSS O0_ARM sr_atoms [] None (mkFacts [(24%nat, o0_PTR)] [] []).
(* Run A (fi_n c >= 2): the shadow byte of s8 (atom 33) at its shadow address (atom 32, the alias fact). *)
Definition o0_rgsh : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition o0_GA : facts :=
  mkFacts [(22%nat, mkAF 1 1 0); (24%nat, o0_PTR); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (27%nat, mkAF 1 (2 ^ 26) 0); (32%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (33%nat, mkAF 0 7 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 24 0) (SLit 3)) (SOff 26 0), SOff 32 0)].
Definition o0_ssA : sstate := mkSS O0_ARM sr_atoms [o0_rgsh] None o0_GA.
(* Case 2 (fi_n c = 2), from +0x618: the byte at s8 (atom 32); s7 is pinned to 2 at the seat. *)
Definition o0_rgb1 : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition o0_G2 : facts :=
  mkFacts [(22%nat, mkAF 1 1 0); (24%nat, o0_PTR); (25%nat, o0_PTR); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 255 0)] [] [].
Definition o0_ss2 : sstate := mkSS O0_618 sr_atoms [o0_rgb1] None o0_G2.
(* Case 3 (fi_n c >= 3), from +0x618: the bytes at s8 and s9 + 2 (atoms 32, 33); s7 = fi_n c >= 3. *)
Definition o0_rgb2 : YP09.region := YP09.mkRegion (Some 25%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 33 0))].
Definition o0_G3 : facts :=
  mkFacts [(22%nat, mkAF 1 1 0); (23%nat, mkAF 3 (2 ^ 26) 0); (24%nat, o0_PTR); (25%nat, o0_PTR);
           (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] [].
Definition o0_ss3 : sstate := mkSS O0_618 sr_atoms [o0_rgb1; o0_rgb2] None o0_G3.
Definition o0_SH3 : list shent := [mkSHE 25 2 3].

(* The value of a symbolic word as the word of a Z, one constructor at a time (decode's cs_den). *)
Lemma o0_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma o0_den_off : forall E n k x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n k x H. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma o0_den_alu : forall E op a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu op a b) = Z_to_bv 64 (zalu64 op x y).
Proof. intros E op a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb. apply zalu64_sound. Qed.
Lemma o0_word_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H. Qed.
Lemma o0_U_off : forall E n k x, bv_unsigned (ew E n) = x -> 0 <= x + k < 2 ^ 64 -> U E (SOff n k) = x + k.
Proof. intros E n k x H Hr. unfold U. rewrite (o0_den_off E n k x H). apply unsigned_lit_small. exact Hr. Qed.
Ltac o0_den :=
  lazymatch goal with
  | |- sv_denot ?E (SLit ?z) = _ => apply o0_den_lit
  | |- sv_denot ?E (SOff ?n ?k) = _ =>
      first
        [ lazymatch goal with Hx : bv_unsigned (ew E n) = _ |- _ => apply (o0_den_off E n k _ Hx) end
        | apply o0_den_off; cbn [ew ewset extK Nat.eqb];
          lazymatch goal with |- bv_unsigned (ew ?E0 n) = _ =>
            lazymatch goal with Hx : bv_unsigned (ew E0 n) = _ |- _ => exact Hx end end ]
  | |- sv_denot ?E (SAlu ?op ?a ?b) = _ => eapply o0_den_alu; o0_den
  end.

Lemma o0_u64 : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 v) = v.
Proof. intros v Hv. apply unsigned_lit_small. exact Hv. Qed.

Section env. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The env of a seat: the registers at its pc, then the values the run reads as atoms 32, 33. *)
Definition o0_E (regs : bvmap 5 word) (xs : list word) : env := Eimg (PI := PI_transportb) (Ereg regs xs).
Lemma o0_E_extra : forall regs xs j, (j < 8)%nat -> ew (o0_E regs xs) (32 + j) = nth j xs (Z_to_bv 64 0).
Proof. intros regs xs j Hj. unfold o0_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
End env.

(* The value of an atom of a seat env that is a register at the seat, from the register's equation R. *)
Ltac o0_at R :=
  lazymatch type of R with YK11.getr ?rg ?r = _ =>
  lazymatch goal with |- bv_unsigned (ew _ ?n) = _ =>
    unfold o0_E; rewrite (can_ew_Eimg_Ereg_nat rg _ n r ltac:(vm_compute; reflexivity)), R; apply o0_u64 end end.
(* The same atom as a word. *)
Ltac o0_ew R :=
  lazymatch type of R with YK11.getr ?rg ?r = _ =>
  lazymatch goal with |- ew _ ?n = _ =>
    unfold o0_E; rewrite (can_ew_Eimg_Ereg_nat rg _ n r ltac:(vm_compute; reflexivity)); exact R end end.

Section seat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* An input byte, as the memory holds it (lc_input's garr8). *)
Lemma o0_inbyte : forall (H : word -> bool) mem p (D : list byte) i,
  garr8 segs (mrestrict H mem) p (map (fun b : byte => bv_unsigned b) D) -> 0 <= i < Z.of_nat (length D) ->
  val_mem segs (mrestrict H mem) (p + i) 1 (DSpec.at8 D (Z.to_nat i)).
Proof.
intros H mem p D i HG Hi.
assert (Hj : (Z.to_nat i < length (map (fun b : byte => bv_unsigned b) D))%nat) by (rewrite length_map; lia).
destruct (HG (Z.to_nat i) Hj) as [Hv _]. rewrite Z2Nat.id in Hv by lia.
replace (DSpec.at8 D (Z.to_nat i)) with (nth (Z.to_nat i) (map (fun b : byte => bv_unsigned b) D) 0); [exact Hv|].
unfold DSpec.at8, DSpec.bz.
rewrite (nth_indep _ 0 ((fun b : byte => bv_unsigned b) (DSpec.b8 0))) by (rewrite length_map; lia).
rewrite map_nth. reflexivity.
Qed.

(* A shadow entry over input bytes [a + lo, a + hi) of a heap block (p0, n0): the block's shadow admits them, and
   they lie in application memory. *)
Lemma o0_sh : forall (LAWS : AR_laws segs B) E (W : world segs) mem ly S md p0 n0 (m : nat) a lo hi,
  @AR rc segs B ly S W mem md -> In (p0, n0) (ablocks B ly S) -> 0 <= n0 ->
  U E o0_Bx = SHADOW_OFF -> U E (SOff m 0) = a ->
  p0 <= a + lo -> a + hi <= p0 + n0 -> lo < hi ->
  shent_ok segs o0_Bx E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros LAWS E W mem ly S md p0 n0 m a lo hi HAR Hin Hn0 HB Hm H1 H2 H3.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4 & Hpc & Happ & _).
pose proof (req_size_pos n0 Hn0) as [Hq1 Hq2].
apply (shent_ok_of_range segs (w_H W) mem E o0_Bx m p0 n0 a lo hi); [| exact HB | exact Hm | lia | lia |].
- apply (range_addressable_of_block segs B LAWS ly S W mem md p0 n0); [exact HAR | exact Hin | lia | lia].
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
  unfold in_app in Happ. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* Case 1's seat: no region; s8 a pointer. *)
Lemma o0_seat1 : forall (W : world segs) regs mem s8,
  YK11.getr regs 24 = w64 s8 -> 4096 <= s8 <= 140737479966720 ->
  st_ok_pi segs VAL (o0_E regs []) o0_ss1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O0_ARM)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem s8 R24 Hs8.
assert (U24 : bv_unsigned (ew (o0_E regs []) 24) = s8) by (o0_at R24; lia).
rewrite restrict_mkst_fx. unfold o0_ss1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- unfold o0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, o0_PTR. cbn [af_lo af_hi af_al2]. rewrite U24.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* Run A's seat: the shadow byte sb of s8 at its shadow address, read only, named by the alias fact. *)
Lemma o0_seatA : forall (W : world segs) regs mem s8 m sb,
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 24 = w64 s8 -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 27 = w64 m ->
  4096 <= s8 <= 140737479966720 -> 1 <= m <= 2 ^ 26 -> 0 <= sb <= 7 ->
  val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + s8 / 8) 1 sb ->
  st_ok_pi segs VAL (o0_E regs [w64 (SHADOW_OFF + s8 / 8); w64 sb]) o0_ssA
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O0_ARM)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem s8 m sb R22 R24 R26 R27 Hs8 Hm Hsb VS.
set (E := o0_E regs [w64 (SHADOW_OFF + s8 / 8); w64 sb]).
assert (HD : 0 <= s8 / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (U22 : bv_unsigned (ew E 22) = 1) by (unfold E; o0_at R22; lia).
assert (U24 : bv_unsigned (ew E 24) = s8) by (unfold E; o0_at R24; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (unfold E; o0_at R26; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = m) by (unfold E; o0_at R27; lia).
assert (E24 : ew E 24 = w64 s8) by (unfold E; o0_ew R24).
assert (E26 : ew E 26 = w64 SHADOW_OFF) by (unfold E; o0_ew R26).
assert (E32 : ew E 32 = w64 (SHADOW_OFF + s8 / 8))
  by (unfold E; pose proof (o0_E_extra regs [w64 (SHADOW_OFF + s8 / 8); w64 sb] 0 ltac:(lia)) as H;
      cbn [Nat.add nth] in H; exact H).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF + s8 / 8) by (rewrite E32; apply o0_u64; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = sb)
  by (unfold E; pose proof (o0_E_extra regs [w64 (SHADOW_OFF + s8 / 8); w64 sb] 1 ltac:(lia)) as H;
      cbn [Nat.add nth] in H; rewrite H; apply o0_u64; lia).
rewrite restrict_mkst_fx. unfold o0_ssA.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- unfold E, o0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, o0_rgsh.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
  split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs _ _ (SHADOW_OFF + s8 / 8) 0 1 (SOff 33 0) sb);
    [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VS].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, o0_rgsh.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. exact (conj I I).
- unfold o0_GA, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, o0_PTR. cbn [af_lo af_hi af_al2]. rewrite U22, U24, U26, U27, U32, U33.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF in *; lia).
  rewrite (can_denot_shadow E 24 26 s8 SHADOW_OFF E24 E26 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)
    ltac:(unfold SHADOW_OFF; lia)).
  cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
Qed.

(* Case 2's seat at +0x618: the byte at s8 = po + 1 (atom 32); s9 = po. *)
Lemma o0_seat2 : forall (W : world segs) regs mem po b1,
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 24 = w64 (po + 1) -> YK11.getr regs 25 = w64 po ->
  YK11.getr regs 26 = w64 SHADOW_OFF ->
  4096 <= po -> po + 1 <= 140737479966720 -> 0 <= b1 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (po + 1) 1 b1 ->
  st_ok_pi segs VAL (o0_E regs [w64 b1]) o0_ss2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O0_618)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem po b1 R22 R24 R25 R26 Hlo Hhi Hb1 V1.
assert (U22 : bv_unsigned (ew (o0_E regs [w64 b1]) 22) = 1) by (o0_at R22; lia).
assert (U24 : bv_unsigned (ew (o0_E regs [w64 b1]) 24) = po + 1) by (o0_at R24; lia).
assert (U25 : bv_unsigned (ew (o0_E regs [w64 b1]) 25) = po) by (o0_at R25; lia).
assert (U26 : bv_unsigned (ew (o0_E regs [w64 b1]) 26) = SHADOW_OFF) by (o0_at R26; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew (o0_E regs [w64 b1]) 32) = b1)
  by (pose proof (o0_E_extra regs [w64 b1] 0 ltac:(lia)) as H; cbn [Nat.add nth] in H; rewrite H; apply o0_u64; lia).
rewrite restrict_mkst_fx. unfold o0_ss2.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- unfold o0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, o0_rgb1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs _ _ (po + 1) 0 1 (SOff 32 0) b1);
    [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V1].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, o0_rgb1.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. exact (conj I I).
- unfold o0_G2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, o0_PTR. cbn [af_lo af_hi af_al2]. rewrite U22, U24, U25, U26, U32.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* Case 3's seat at +0x618: the bytes at s8 = po + 1 and s9 + 2 = po + 2 (atoms 32, 33); s7 = n. *)
Lemma o0_seat3 : forall (W : world segs) regs mem po n b1 b2,
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 n -> YK11.getr regs 24 = w64 (po + 1) ->
  YK11.getr regs 25 = w64 po -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  3 <= n <= 2 ^ 26 -> 4096 <= po -> po + 3 <= 140737479966720 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (po + 1) 1 b1 -> val_mem segs (mrestrict (w_H W) mem) (po + 2) 1 b2 ->
  st_ok_pi segs VAL (o0_E regs [w64 b1; w64 b2]) o0_ss3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O0_618)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem po n b1 b2 R22 R23 R24 R25 R26 Hn Hlo Hhi Hb1 Hb2 V1 V2.
assert (U22 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 22) = 1) by (o0_at R22; lia).
assert (U23 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 23) = n) by (o0_at R23; lia).
assert (U24 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 24) = po + 1) by (o0_at R24; lia).
assert (U25 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 25) = po) by (o0_at R25; lia).
assert (U26 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 26) = SHADOW_OFF) by (o0_at R26; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 32) = b1)
  by (pose proof (o0_E_extra regs [w64 b1; w64 b2] 0 ltac:(lia)) as H; cbn [Nat.add nth] in H; rewrite H;
      apply o0_u64; lia).
assert (U33 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 33) = b2)
  by (pose proof (o0_E_extra regs [w64 b1; w64 b2] 1 ltac:(lia)) as H; cbn [Nat.add nth] in H; rewrite H;
      apply o0_u64; lia).
rewrite restrict_mkst_fx. unfold o0_ss3.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- unfold o0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, o0_rgb1.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ (po + 1) 0 1 (SOff 32 0) b1);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V1].
  + unfold region_ok, o0_rgb2.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U25.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ po 2 1 (SOff 33 0) b2);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact V2].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, o0_rgb1, o0_rgb2.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U25.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold o0_G3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, o0_PTR. cbn [af_lo af_hi af_al2]. rewrite U22, U23, U24, U25, U26, U32, U33.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

End seat.

(* ------------------------------------------------------------------ *)
(* 3. The engine's helpers and the refuted branches                     *)
(* ------------------------------------------------------------------ *)

(* The write rights of a run from a seat whose regions are all read-only: none is needed. *)
Ltac o0_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* A run from such a seat leaves the memory as it found it (its frame has no window). *)
Ltac o0_mem HF :=
  apply functional_extensionality; let x := fresh "x" in intros x; apply HF;
  let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw);
  lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia |]);
  destruct Hr.

(* Name the machine state of HS. *)
Ltac o0_name HS x :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x end.

(* After a run: the model generalized, and EM : the run's last memory is the one it started from. *)
Ltac o0_post HF HFr HG EM :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdr" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end;
  lazymatch type of HF with frame_of _ _ ?m1 ?m2 => assert (EM : m2 = m1) by (o0_mem HF) end;
  clear HF HFr HG.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac o0_rd HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?valx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* `slli a2, a2, 8; or a1, a2, a1` of the two bytes: the length word. *)
Lemma o0_zw : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> zalu64 ALU_OR (zalu64 ALU_SLL x 8) y = y + 256 * x.
Proof.
intros x y Hx Hy. unfold zalu64, zalu_raw, zcanon, M64.
rewrite (Z.mod_small x (2 ^ 64)) by lia. rewrite (Z.mod_small 8 (2 ^ 64)) by lia.
change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia.
rewrite !(Z.mod_small (x * 2 ^ 8) (2 ^ 64)) by lia. rewrite (Z.mod_small y (2 ^ 64)) by lia.
rewrite (o0_lor8 x y Hx Hy). rewrite Z.mod_small by lia. lia.
Qed.

(* An unsigned compare of two words of Zs in range. *)
Lemma o0_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
intros x y Hx Hy. unfold bv_ltu. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* `not a0, s8` (xori -1). *)
Lemma o0_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> zalu64 ALU_XOR x (-1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. unfold zalu64, zalu_raw, zcanon, M64. rewrite (Z.mod_small x (2 ^ 64)) by lia.
change ((-1) mod 2 ^ 64) with (Z.ones 64). rewrite YE2y.lxor_ones by lia.
rewrite Z.ones_equiv, Z.mod_small by lia. lia.
Qed.

(* The UBSan test of the take, `bltu a0, a1` with a0 = ~s8 and a1 the length: never taken, both below 2 ^ 47. *)
Lemma o0_ltu_take : forall x y, 0 <= x < 2 ^ 47 -> 0 <= y < 2 ^ 47 ->
  bv_ltu (Z_to_bv 64 (zalu64 ALU_XOR x (-1))) (Z_to_bv 64 y) = false.
Proof.
intros x y Hx Hy. rewrite (o0_xor_m1 x) by lia. rewrite o0_ltu by lia. apply Z.ltb_ge. lia.
Qed.

(* The slow path of the first byte's check, `bge a1, a0` with a1 = s8 & 7 and a0 = sb, the shadow byte of s8, not 0:
   the shadow admits the byte (s8 mod 8 < sb), so the branch to the report call 0x82f2c is not taken. *)
Lemma o0_bge : forall x sb, 0 <= x < 2 ^ 64 -> 0 < sb < 8 -> x mod 8 < sb ->
  branch_taken BC_GE (Z_to_bv 64 (zalu64 ALU_AND x 7)) (Z_to_bv 64 sb) = false.
Proof.
intros x sb Hx Hsb Hlt.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
assert (EA : zalu64 ALU_AND x 7 = x mod 8).
{ unfold zalu64, zalu_raw, zcanon, M64. rewrite (Z.mod_small x (2 ^ 64)) by lia.
  change (7 mod 2 ^ 64) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  apply Z.mod_small. lia. }
rewrite EA. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite (signed_of_small (Z_to_bv 64 (x mod 8))) by (rewrite unsigned_lit_small by lia; unfold half64; lia).
rewrite (signed_of_small (Z_to_bv 64 sb)) by (rewrite unsigned_lit_small by lia; unfold half64; lia).
rewrite !unsigned_lit_small by lia.
destruct (Z.ltb_spec (x mod 8) sb); [reflexivity | exfalso; lia].
Qed.

(* `beqz` on a register atom m holding n: the test n = 0. *)
Lemma o0_beqz : forall E (m : nat) n b, ew E m = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff m 0)) (sv_denot E (SLit 0)) = b -> (n =? 0) = b.
Proof.
intros E m n b Hm Hn Hb. rewrite <- Hb.
rewrite (denot_lit_U E (SOff m 0)), U_SOff, Hm, unsigned_lit_small by lia. rewrite Z.add_0_r, (zcanon_id n) by (unfold M64; lia).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). cbn [branch_taken].
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* A register value  sv_denot E e = w64 x. *)
Ltac o0_rval :=
  unfold w64; etransitivity; [o0_den|]; rewrite ?Z.add_0_r; rewrite ?o0_zw by lia; apply o0_word_eq;
  unfold zalu64, zalu_raw, zcanon, M64; rewrite ?Z.add_0_r;
  first [reflexivity | f_equal; lia | Z.div_mod_to_equations; lia].

(* env_agree 32 (Ereg regs xs) Ex for the env Ex of a run seated at E = o0_E regs xs. *)
Ltac o0_agree E :=
  split;
  [ let n := fresh "n" in let Hn := fresh "Hn" in
    intros n Hn; cbn [ew ewset extK];
    repeat (match goal with |- context [Nat.eqb n ?m] => destruct (Nat.eqb_spec n m); [lia|] end);
    unfold E, o0_E; apply Eimg_low; unfold A_TEXT; lia
  | reflexivity ].

(* The taken side of the take's UBSan test `bltu a0, a1` (a0 = ~X, a1 = Y): refuted. *)
Ltac o0_take_refute X Y :=
  exfalso;
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex ?a) (sv_denot ?Ex ?b) = true |- _ =>
    let Da := fresh "Da" in let Db := fresh "Db" in
    assert (Da : sv_denot Ex a = Z_to_bv 64 (zalu64 ALU_XOR X (-1)))
      by (etransitivity; [o0_den|]; rewrite ?Z.add_0_r; reflexivity);
    assert (Db : sv_denot Ex b = Z_to_bv 64 Y)
      by (etransitivity; [o0_den|]; rewrite ?Z.add_0_r; rewrite ?o0_zw by lia;
          first [reflexivity | apply o0_word_eq; f_equal; lia]);
    cbn [branch_taken] in Hc; rewrite Da, Db, o0_ltu_take in Hc by lia; discriminate Hc
  end.

(* ------------------------------------------------------------------ *)
(* 4. The segment                                                       *)
(* ------------------------------------------------------------------ *)

Section op0. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* lc_lcore holds of any registers that agree on the ones it names (sp, gp, tp, s0, s1, s2, s3, s10). *)
Lemma o0_lcore_regs : forall cx op k ly S (W : world segs) regs mem md e regs2,
  lc_lcore B MT cx op false false k ly S W regs mem md e ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 26%bv] -> YK11.getr regs2 r = YK11.getr regs r) ->
  lc_lcore B MT cx op false false k ly S W regs2 mem md e.
Proof.
intros cx op k ly S W regs mem md e regs2 HL RR.
destruct HL as (HC & (F18 & F26) & HSP & HFSH & HOK & HE & HM & R19).
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hrest).
refine (conj (conj HJ (conj Hfrs (conj HlyF (conj HPERM (conj _ (conj _ (conj _ (conj _ (conj _ Hrest)))))))))
  (conj (conj _ _) (conj HSP (conj HFSH (conj HOK (conj HE (conj HM _))))))).
- exact (eq_trans (RR 2%bv ltac:(cbn; tauto)) Rsp).
- exact (eq_trans (RR 8%bv ltac:(cbn; tauto)) R8).
- exact (eq_trans (RR 9%bv ltac:(cbn; tauto)) R9).
- exact (eq_trans (RR 3%bv ltac:(cbn; tauto)) Rgp).
- exact (eq_trans (RR 4%bv ltac:(cbn; tauto)) Rtp).
- exact (eq_trans (RR 18%bv ltac:(cbn; tauto)) F18).
- exact (eq_trans (RR 26%bv ltac:(cbn; tauto)) F26).
- exact (eq_trans (RR 19%bv ltac:(cbn; tauto)) R19).
Qed.

(* The cut from the facts the runs leave. *)
Lemma o0_close : forall cx op ly S (W : world segs) mem md e regs2 rv,
  lc_lcore B MT cx op false false (lo_k op) ly S W regs2 mem md e ->
  lc_tw W mem (lo_B op) ->
  lc_opc (l_pl cx) (lo_c op) = 0 ->
  lc_recv_vals (l_pl cx) (lo_c op) = rv ->
  YK11.getr regs2 10 = w64 (l_p cx + rv_off rv) -> YK11.getr regs2 11 = w64 (rv_n rv) ->
  YK11.getr regs2 12 = w64 (rv_bp rv) -> YK11.getr regs2 13 = w64 (rv_pf rv) ->
  YK11.getr regs2 21 = w64 (l_p cx + TOP.fi_off (rv_c rv)) -> YK11.getr regs2 27 = w64 (TOP.fi_n (rv_c rv)) ->
  YK11.getr regs2 20 = w64 (lc_F cx + 32) -> YK11.getr regs2 22 = w64 1 ->
  lc_st_recv B MT cx op W (lc_cfg cx LO_RECV regs2 mem md).
Proof.
intros cx op ly S W mem md e regs2 rv HL Htw Ho Erv R10 R11 R12 R13 R21 R27 R20 R22.
exists ly, S, regs2, mem, md, e. cbv zeta. rewrite Erv.
split; [reflexivity|]. split; [left; exact Ho|]. split; [exact HL|]. split; [exact Htw|].
split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
split; [split; [exact R21 | exact R27]|]. split; [exact R20 | exact R22].
Qed.

Lemma lc_op0_ok : lc_op0_stmt B MT XL RLO RHI.
Proof.
unfold lc_op0_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & -> & Ho & HL & Htw & Hc0 & Hc1 & R20 & R22).
symmetry in Ho.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HL as (HC & (R18 & R26) & _ & _ & (_ & _ & HCok & Hn0 & _) & _ & _ & R19).
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HPAY & _)).
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as [HAR _ _ _ _ _ (Hln & Hlen) HIN _].
destruct HCok as (Hoff & Hn & Hsum).
rewrite (o0_oc (l_pl cx) (lo_c op) Hn0) in Hc1.
destruct Hc0 as (R25 & R23). destruct Hc1 as (R24 & R27). cbn [TOP.fi_off TOP.fi_n] in R24, R27.
assert (Hin : In (l_p cx, l_n cx) (ablocks B ly' S')) by (apply HIN; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4 & Hpc & _).
pose proof (req_size_pos (l_n cx) ltac:(lia)) as [Hq1 Hq2].
pose proof (@alloc_ceiling_value rc) as ((_ & Hceil) & _).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
change (SRr segs W' (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + O0_ARM)) mem' (YK11.seg_rom segs)) md')
  (lc_st_recv B MT cx op)).
rewrite Z.add_assoc in R24.
destruct (Z.eq_dec (TOP.fi_n (lo_c op)) 1) as [E1 | E1].
- (* fi_n c = 1: no byte after the op byte; s11 = 0 *)
  set (E := o0_E regs' []).
  pose proof (@o0_seat1 (l_fx cx) rc W' regs' mem' (l_p cx + TOP.fi_off (lo_c op) + 1) R24 ltac:(lia)) as HS0.
  fold E in HS0.
  pose proof (st_ok_pi_pin_reg' E o0_ss1 _ 27%bv 0 HS0
    ltac:(cbn [ms_regs restrict YK11.mkst]; rewrite E1 in R27; exact R27) eq_refl) as HS.
  clear HS0.
  assert (SHOK : sh_ok segs o0_Bx [] E (mrestrict (w_H W') mem')) by constructor.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, o0_E; apply Eimg_env).
  assert (A24 : bv_unsigned (ew E 24) = l_p cx + TOP.fi_off (lo_c op) + 1) by (unfold E; o0_at R24; lia).
  (* +0x5f4 .. +0xbe8: `beqz s11` taken, s7 = a1 = a2 = 0, `bltu a1, s7` not taken, a1 = 0, a0 = ~s8, the take test *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { o0_awr. }
  o0_name HS msA. o0_post HF HFr HG EMA.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + o0_take_refute (l_p cx + TOP.fi_off (lo_c op) + 1) 0.
  + clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_RECV.
    { o0_awr. }
    o0_name HS msB. o0_post HF HFr HG EMB.
    (* +0xc00: a0 = s5 = s8, a1 = a2 = a3 = s11 = 0 *)
    o0_rd HS (10%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 1))) X10 o0_rval.
    o0_rd HS (11%bv : bv 5) (w64 0) X11 o0_rval.
    o0_rd HS (12%bv : bv 5) (w64 0) X12 o0_rval.
    o0_rd HS (13%bv : bv 5) (w64 0) X13 o0_rval.
    o0_rd HS (21%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 1))) X21 o0_rval.
    o0_rd HS (27%bv : bv 5) (w64 0) X27 o0_rval.
    assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 26%bv] ->
      YK11.getr (ms_regs msB) r = YK11.getr regs' r).
    { intros r Hr. refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') msB) regs' [] _ HS _ _ r Hr);
        [o0_agree E | vm_compute; reflexivity]. }
    pmkst HS. apply SRr_ret. rewrite EMB, EMA in HJ |- *.
    apply (o0_close cx op ly' S' W' mem' _ e (ms_regs msB)
      (mkLrv 0 0 (TOP.fi_off (lo_c op) + 1) 0 (TOP.FuzzIn (TOP.fi_off (lo_c op) + 1) 0))).
    * apply (o0_lcore_regs cx op (lo_k op) ly' S' W' regs' mem' _ e (ms_regs msB)).
      -- destruct HL as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
      -- intros r Hr. apply KR. cbn in Hr |- *. tauto.
    * exact Htw.
    * exact Ho.
    * exact (o0_rv1 (l_pl cx) (lo_c op) E1 Ho).
    * exact X10.
    * exact X11.
    * exact X12.
    * exact X13.
    * exact X21.
    * exact X27.
    * exact (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20).
    * exact (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22).
- (* fi_n c >= 2 *)
  assert (Hn2 : 2 <= TOP.fi_n (lo_c op)) by lia.
  (* The walk from +0x618 (the first byte's check passed): the registers of the arm but a0 / a1. *)
  assert (CONT : forall (regs2 : bvmap 5 word) (md2 : Model),
    lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md2 e ->
    (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv;
                           27%bv] -> YK11.getr regs2 r = YK11.getr regs' r) ->
    SRr segs W' (mkCfg (@YK11.mkst (l_fx cx) regs2 (Z_to_bv 64 (BASE + O0_618)) mem' (YK11.seg_rom segs)) md2)
      (lc_st_recv B MT cx op)).
  { intros regs2 md2 HL2 KR2.
    pose proof HL2 as ((HJ2 & _) & _). clear HJ. rename HJ2 into HJ.
    assert (Q22 : YK11.getr regs2 22 = w64 1) by exact (eq_trans (KR2 22%bv ltac:(cbn; tauto)) R22).
    assert (Q23 : YK11.getr regs2 23 = w64 (TOP.fi_n (lo_c op))) by exact (eq_trans (KR2 23%bv ltac:(cbn; tauto)) R23).
    assert (Q24 : YK11.getr regs2 24 = w64 (l_p cx + TOP.fi_off (lo_c op) + 1))
      by exact (eq_trans (KR2 24%bv ltac:(cbn; tauto)) R24).
    assert (Q25 : YK11.getr regs2 25 = w64 (l_p cx + TOP.fi_off (lo_c op)))
      by exact (eq_trans (KR2 25%bv ltac:(cbn; tauto)) R25).
    assert (Q26 : YK11.getr regs2 26 = w64 SHADOW_OFF) by exact (eq_trans (KR2 26%bv ltac:(cbn; tauto)) R26).
    remember (DSpec.at8 (l_pl cx) (Z.to_nat (TOP.fi_off (lo_c op) + 1))) as b1 eqn:Eb1.
    assert (Hb1 : 0 <= b1 < 256) by (rewrite Eb1; apply o0_at8).
    assert (V1 : val_mem segs (mrestrict (w_H W') mem') (l_p cx + TOP.fi_off (lo_c op) + 1) 1 b1).
    { rewrite Eb1, <- Z.add_assoc.
      exact (o0_inbyte (w_H W') mem' (l_p cx) (l_pl cx) (TOP.fi_off (lo_c op) + 1) HPAY ltac:(lia)). }
    destruct (Z.eq_dec (TOP.fi_n (lo_c op)) 2) as [E2 | E2].
    - (* fi_n c = 2: one byte after the op byte *)
      set (E := o0_E regs2 [w64 b1]).
      pose proof (@o0_seat2 (l_fx cx) rc W' regs2 mem' (l_p cx + TOP.fi_off (lo_c op)) b1 Q22 Q24 Q25 Q26
        ltac:(lia) ltac:(lia) Hb1 V1) as HS0. fold E in HS0.
      pose proof (st_ok_pi_pin_reg' E o0_ss2 _ 23%bv 2 HS0
        ltac:(cbn [ms_regs restrict YK11.mkst]; rewrite E2 in Q23; exact Q23) eq_refl) as HS.
      clear HS0.
      assert (A25 : bv_unsigned (ew E 25) = l_p cx + TOP.fi_off (lo_c op)) by (unfold E; o0_at Q25; lia).
      assert (SHOK : sh_ok segs o0_Bx [] E (mrestrict (w_H W') mem')) by constructor.
      assert (HEI : img_env VAL A_LIM E) by (unfold E, o0_E; apply Eimg_env).
      (* +0x618 .. +0xbe8: a1 = the byte, s8 = s9 + 2, `bne s7, 2` not taken, s7 = a2 = 0, `bltu a1, s7` not
         taken, a1 = 0, a0 = ~s8, the take test *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { o0_awr. }
      o0_name HS msA. o0_post HF HFr HG EMA.
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
      + o0_take_refute (l_p cx + TOP.fi_off (lo_c op) + 2) 0.
      + clear Hc.
        paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_RECV.
        { o0_awr. }
        o0_name HS msB. o0_post HF HFr HG EMB.
        (* +0xc00: a0 = s5 = s9 + 2, a1 = a2 = a3 = s11 = 0 *)
        o0_rd HS (10%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 2))) X10 o0_rval.
        o0_rd HS (11%bv : bv 5) (w64 0) X11 o0_rval.
        o0_rd HS (12%bv : bv 5) (w64 0) X12 o0_rval.
        o0_rd HS (13%bv : bv 5) (w64 0) X13 o0_rval.
        o0_rd HS (21%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 2))) X21 o0_rval.
        o0_rd HS (27%bv : bv 5) (w64 0) X27 o0_rval.
        assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 26%bv] ->
          YK11.getr (ms_regs msB) r = YK11.getr regs' r).
        { intros r Hr. rewrite <- (KR2 r ltac:(cbn in Hr |- *; tauto)).
          refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') msB) regs2 [w64 b1] _ HS _ _ r Hr);
            [o0_agree E | vm_compute; reflexivity]. }
        pmkst HS. apply SRr_ret. rewrite EMB, EMA in HJ |- *.
        apply (o0_close cx op ly' S' W' mem' _ e (ms_regs msB)
          (mkLrv 0 0 (TOP.fi_off (lo_c op) + 2) 0 (TOP.FuzzIn (TOP.fi_off (lo_c op) + 2) 0))).
        * apply (o0_lcore_regs cx op (lo_k op) ly' S' W' regs' mem' _ e (ms_regs msB)).
          -- destruct HL2 as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
          -- intros r Hr. apply KR. cbn in Hr |- *. tauto.
        * exact Htw.
        * exact Ho.
        * exact (o0_rv2 (l_pl cx) (lo_c op) E2 Ho).
        * exact X10.
        * exact X11.
        * exact X12.
        * exact X13.
        * exact X21.
        * exact X27.
        * exact (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20).
        * exact (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22).
    - (* fi_n c >= 3: two bytes after the op byte *)
      assert (Hn3 : 3 <= TOP.fi_n (lo_c op)) by lia.
      remember (DSpec.at8 (l_pl cx) (Z.to_nat (TOP.fi_off (lo_c op) + 2))) as b2 eqn:Eb2.
      assert (Hb2 : 0 <= b2 < 256) by (rewrite Eb2; apply o0_at8).
      assert (V2 : val_mem segs (mrestrict (w_H W') mem') (l_p cx + TOP.fi_off (lo_c op) + 2) 1 b2).
      { rewrite Eb2, <- Z.add_assoc.
        exact (o0_inbyte (w_H W') mem' (l_p cx) (l_pl cx) (TOP.fi_off (lo_c op) + 2) HPAY ltac:(lia)). }
      set (E := o0_E regs2 [w64 b1; w64 b2]).
      pose proof (@o0_seat3 (l_fx cx) rc W' regs2 mem' (l_p cx + TOP.fi_off (lo_c op)) (TOP.fi_n (lo_c op)) b1 b2
        Q22 Q23 Q24 Q25 Q26 ltac:(lia) ltac:(lia) ltac:(lia) Hb1 Hb2 V1 V2) as HS. fold E in HS.
      assert (A23 : bv_unsigned (ew E 23) = TOP.fi_n (lo_c op)) by (unfold E; o0_at Q23; lia).
      assert (A25 : bv_unsigned (ew E 25) = l_p cx + TOP.fi_off (lo_c op)) by (unfold E; o0_at Q25; lia).
      assert (A26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (unfold E; o0_at Q26; unfold SHADOW_OFF; lia).
      assert (A32 : bv_unsigned (ew E 32) = b1)
        by (unfold E; pose proof (o0_E_extra regs2 [w64 b1; w64 b2] 0 ltac:(lia)) as H; cbn [Nat.add nth] in H;
            rewrite H; apply o0_u64; lia).
      assert (A33 : bv_unsigned (ew E 33) = b2)
        by (unfold E; pose proof (o0_E_extra regs2 [w64 b1; w64 b2] 1 ltac:(lia)) as H; cbn [Nat.add nth] in H;
            rewrite H; apply o0_u64; lia).
      assert (SHOK : sh_ok segs o0_Bx o0_SH3 E (mrestrict (w_H W') mem')).
      { unfold sh_ok, o0_SH3. apply Forall_cons; [|apply Forall_nil].
        apply (o0_sh B LAWS E W' mem' ly' S' md' (l_p cx) (l_n cx) 25 (l_p cx + TOP.fi_off (lo_c op)) 2 3 HAR Hin);
          [ lia
          | unfold o0_Bx; rewrite (o0_U_off E 26 0 SHADOW_OFF A26) by (unfold SHADOW_OFF; lia); reflexivity
          | rewrite (o0_U_off E 25 0 _ A25) by lia; apply Z.add_0_r
          | lia | lia | lia ]. }
      assert (HEI : img_env VAL A_LIM E) by (unfold E, o0_E; apply Eimg_env).
      (* +0x618 .. +0xbdc: a1 = the first byte, s8 = s9 + 2, `bne s7, 2` taken, the cursor test (not taken), the
         checked load of the byte at s9 + 2, s7 -= 3, s8 = s9 + 3, a1 = the length word, `bltu a1, s7` *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { o0_awr. }
      o0_name HS msA. o0_post HF HFr HG EMA.
      assert (Ew : o0_w (l_pl cx) (TOP.fi_off (lo_c op)) = b1 + 256 * b2)
        by (unfold o0_w; rewrite <- Eb1, <- Eb2; reflexivity).
      assert (Hwr : 0 <= b1 + 256 * b2 < 65536) by lia.
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
      + (* taken: the length word is below the bytes left *)
        assert (Hlt : b1 + 256 * b2 < TOP.fi_n (lo_c op) - 3).
        { lazymatch type of Hc with branch_taken _ (sv_denot ?Ex ?a) (sv_denot ?Ex ?b) = _ =>
            assert (Da : sv_denot Ex a = Z_to_bv 64 (b1 + 256 * b2)) by (etransitivity; [o0_den|];
              rewrite !Z.add_0_r, o0_zw by lia; reflexivity);
            assert (Db : sv_denot Ex b = Z_to_bv 64 (TOP.fi_n (lo_c op) - 3)) by (etransitivity; [o0_den|];
              f_equal; lia) end.
          cbn [branch_taken] in Hc. rewrite Da, Db, o0_ltu in Hc by lia. apply Z.ltb_lt in Hc. exact Hc. }
        clear Hc.
        assert (EL : o0_len (l_pl cx) (TOP.fi_off (lo_c op)) (TOP.fi_n (lo_c op)) = b1 + 256 * b2).
        { unfold o0_len. rewrite Ew. rewrite (proj2 (Z.ltb_lt _ _) Hlt). reflexivity. }
        (* +0xbe4 .. +0xbe8: a0 = ~s8, the take test *)
        paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
        { o0_awr. }
        o0_name HS msB. o0_post HF HFr HG EMB.
        psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
        * o0_take_refute (l_p cx + TOP.fi_off (lo_c op) + 3) (b1 + 256 * b2).
        * clear Hc.
          paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_RECV.
          { o0_awr. }
          o0_name HS msC. o0_post HF HFr HG EMC.
          (* +0xc00: a0 = s9 + 3, a1 = the length word, s5 = s8 + a1, s11 = s7 - a1, a2 = a3 = 0 *)
          o0_rd HS (10%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 3))) X10 o0_rval.
          o0_rd HS (11%bv : bv 5) (w64 (b1 + 256 * b2)) X11 o0_rval.
          o0_rd HS (12%bv : bv 5) (w64 0) X12 o0_rval.
          o0_rd HS (13%bv : bv 5) (w64 0) X13 o0_rval.
          o0_rd HS (21%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 3 + (b1 + 256 * b2)))) X21 o0_rval.
          o0_rd HS (27%bv : bv 5) (w64 (TOP.fi_n (lo_c op) - 3 - (b1 + 256 * b2))) X27 o0_rval.
          assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 26%bv] ->
            YK11.getr (ms_regs msC) r = YK11.getr regs' r).
          { intros r Hr. rewrite <- (KR2 r ltac:(cbn in Hr |- *; tauto)).
            refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') msC) regs2 [w64 b1; w64 b2] _ HS _ _ r Hr);
              [o0_agree E | vm_compute; reflexivity]. }
          pmkst HS. apply SRr_ret. rewrite EMC, EMB, EMA in HJ |- *.
          apply (o0_close cx op ly' S' W' mem' _ e (ms_regs msC)
            (mkLrv 0 0 (TOP.fi_off (lo_c op) + 3) (b1 + 256 * b2)
               (TOP.FuzzIn (TOP.fi_off (lo_c op) + 3 + (b1 + 256 * b2)) (TOP.fi_n (lo_c op) - 3 - (b1 + 256 * b2))))).
          -- apply (o0_lcore_regs cx op (lo_k op) ly' S' W' regs' mem' _ e (ms_regs msC)).
             ++ destruct HL2 as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
             ++ intros r Hr. apply KR. cbn in Hr |- *. tauto.
          -- exact Htw.
          -- exact Ho.
          -- rewrite (o0_rv3 (l_pl cx) (lo_c op) Hn3 Ho), EL. reflexivity.
          -- exact X10.
          -- exact X11.
          -- exact X12.
          -- exact X13.
          -- exact X21.
          -- exact X27.
          -- exact (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20).
          -- exact (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22).
      + (* not taken: the length is the bytes left *)
        assert (Hge : TOP.fi_n (lo_c op) - 3 <= b1 + 256 * b2).
        { lazymatch type of Hc with branch_taken _ (sv_denot ?Ex ?a) (sv_denot ?Ex ?b) = _ =>
            assert (Da : sv_denot Ex a = Z_to_bv 64 (b1 + 256 * b2)) by (etransitivity; [o0_den|];
              rewrite !Z.add_0_r, o0_zw by lia; reflexivity);
            assert (Db : sv_denot Ex b = Z_to_bv 64 (TOP.fi_n (lo_c op) - 3)) by (etransitivity; [o0_den|];
              f_equal; lia) end.
          cbn [branch_taken] in Hc. rewrite Da, Db, o0_ltu in Hc by lia. apply Z.ltb_ge in Hc. exact Hc. }
        clear Hc.
        assert (EL : o0_len (l_pl cx) (TOP.fi_off (lo_c op)) (TOP.fi_n (lo_c op)) = TOP.fi_n (lo_c op) - 3).
        { unfold o0_len. rewrite Ew. rewrite (proj2 (Z.ltb_ge _ _) Hge). reflexivity. }
        (* +0xbe0 .. +0xbe8: a1 = s7, a0 = ~s8, the take test *)
        paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
        { o0_awr. }
        o0_name HS msB. o0_post HF HFr HG EMB.
        psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
        * o0_take_refute (l_p cx + TOP.fi_off (lo_c op) + 3) (TOP.fi_n (lo_c op) - 3).
        * clear Hc.
          paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_RECV.
          { o0_awr. }
          o0_name HS msC. o0_post HF HFr HG EMC.
          (* +0xc00: a0 = s9 + 3, a1 = s7 = the bytes left, s5 = s8 + a1, s11 = 0, a2 = a3 = 0 *)
          o0_rd HS (10%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 3))) X10 o0_rval.
          o0_rd HS (11%bv : bv 5) (w64 (TOP.fi_n (lo_c op) - 3)) X11 o0_rval.
          o0_rd HS (12%bv : bv 5) (w64 0) X12 o0_rval.
          o0_rd HS (13%bv : bv 5) (w64 0) X13 o0_rval.
          o0_rd HS (21%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 3 + (TOP.fi_n (lo_c op) - 3)))) X21 o0_rval.
          o0_rd HS (27%bv : bv 5) (w64 (TOP.fi_n (lo_c op) - 3 - (TOP.fi_n (lo_c op) - 3))) X27 o0_rval.
          assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 26%bv] ->
            YK11.getr (ms_regs msC) r = YK11.getr regs' r).
          { intros r Hr. rewrite <- (KR2 r ltac:(cbn in Hr |- *; tauto)).
            refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') msC) regs2 [w64 b1; w64 b2] _ HS _ _ r Hr);
              [o0_agree E | vm_compute; reflexivity]. }
          pmkst HS. apply SRr_ret. rewrite EMC, EMB, EMA in HJ |- *.
          apply (o0_close cx op ly' S' W' mem' _ e (ms_regs msC)
            (mkLrv 0 0 (TOP.fi_off (lo_c op) + 3) (TOP.fi_n (lo_c op) - 3)
               (TOP.FuzzIn (TOP.fi_off (lo_c op) + 3 + (TOP.fi_n (lo_c op) - 3))
                           (TOP.fi_n (lo_c op) - 3 - (TOP.fi_n (lo_c op) - 3))))).
          -- apply (o0_lcore_regs cx op (lo_k op) ly' S' W' regs' mem' _ e (ms_regs msC)).
             ++ destruct HL2 as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
             ++ intros r Hr. apply KR. cbn in Hr |- *. tauto.
          -- exact Htw.
          -- exact Ho.
          -- rewrite (o0_rv3 (l_pl cx) (lo_c op) Hn3 Ho), EL. reflexivity.
          -- exact X10.
          -- exact X11.
          -- exact X12.
          -- exact X13.
          -- exact X21.
          -- exact X27.
          -- exact (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20).
          -- exact (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22). }
  (* Run A: from the arm to +0x618, through the check of the byte at s8. Its shadow byte sb: *)
  pose proof (range_addressable_of_block segs B LAWS ly' S' W' mem' md' (l_p cx) (l_n cx)
    (l_p cx + TOP.fi_off (lo_c op) + 1) 1 HAR Hin ltac:(lia) ltac:(lia)) as HRA.
  destruct (HRA (l_p cx + TOP.fi_off (lo_c op) + 1) ltac:(lia)) as (sb & Hsb & Hsok).
  unfold shadow_of_addr in Hsb.
  pose proof (Z.mod_pos_bound (l_p cx + TOP.fi_off (lo_c op) + 1) 8 ltac:(lia)) as Hm8.
  assert (Hsbr : 0 <= sb <= 7) by (destruct Hsok as [-> | (H1 & H2)]; lia).
  pose proof (YE2y.val_mem1_of_aview (w_H W') mem' _ _ Hsb) as VS.
  set (E := o0_E regs' [w64 (SHADOW_OFF + (l_p cx + TOP.fi_off (lo_c op) + 1) / 8); w64 sb]).
  pose proof (@o0_seatA (l_fx cx) rc W' regs' mem' (l_p cx + TOP.fi_off (lo_c op) + 1) (TOP.fi_n (lo_c op) - 1) sb
    R22 R24 R26 R27 ltac:(lia) ltac:(lia) Hsbr VS) as HS. fold E in HS.
  assert (A24 : bv_unsigned (ew E 24) = l_p cx + TOP.fi_off (lo_c op) + 1) by (unfold E; o0_at R24; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 sb)
    by (unfold E; pose proof (o0_E_extra regs' [w64 (SHADOW_OFF + (l_p cx + TOP.fi_off (lo_c op) + 1) / 8); w64 sb] 1
          ltac:(lia)) as H; cbn [Nat.add nth] in H; exact H).
  assert (A33 : bv_unsigned (ew E 33) = sb) by (rewrite E33; apply o0_u64; lia).
  assert (SHOK : sh_ok segs o0_Bx [] E (mrestrict (w_H W') mem')) by constructor.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, o0_E; apply Eimg_env).
  (* +0x5f4 .. +0x610: `beqz s11` not taken, the cursor test (not taken), the shadow byte, `beqz a0` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { o0_awr. }
  o0_name HS msA. o0_post HF HFr HG EMA.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* sb = 0: the load at +0x618 *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_618.
    { o0_awr. }
    o0_name HS msB. o0_post HF HFr HG EMB.
    assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 24%bv;
      25%bv; 26%bv; 27%bv] -> YK11.getr (ms_regs msB) r = YK11.getr regs' r).
    { intros r Hr. refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') msB) regs'
        [w64 (SHADOW_OFF + (l_p cx + TOP.fi_off (lo_c op) + 1) / 8); w64 sb] _ HS _ _ r Hr);
        [o0_agree E | vm_compute; reflexivity]. }
    pmkst HS. rewrite EMB, EMA in HJ |- *.
    apply (CONT (ms_regs msB) _).
    * destruct HL as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
    * exact KR.
  + (* sb <> 0: the slow path +0x16f4 .. +0x16fc *)
    pose proof (o0_beqz E 33 sb false E33 ltac:(lia) Hc) as Hs0. apply Z.eqb_neq in Hs0. clear Hc.
    assert (Hx8 : (l_p cx + TOP.fi_off (lo_c op) + 1) mod 8 < sb) by (destruct Hsok as [H0 | (H1 & H2)]; lia).
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { o0_awr. }
    o0_name HS msB. o0_post HF HFr HG EMB.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* `bge a1, a0` taken: the report call 0x82f2c, refuted *)
      exfalso.
      lazymatch goal with Hc : branch_taken BC_GE (sv_denot ?Ex ?a) (sv_denot ?Ex ?b) = true |- _ =>
        assert (Da : sv_denot Ex a = Z_to_bv 64 (zalu64 ALU_AND (l_p cx + TOP.fi_off (lo_c op) + 1) 7))
          by (etransitivity; [o0_den|]; rewrite ?Z.add_0_r; reflexivity);
        assert (Db : sv_denot Ex b = Z_to_bv 64 sb) by (etransitivity; [o0_den|]; rewrite ?Z.add_0_r; reflexivity);
        rewrite Da, Db, (o0_bge (l_p cx + TOP.fi_off (lo_c op) + 1) sb ltac:(lia) ltac:(lia) Hx8) in Hc;
        discriminate Hc
      end.
    * clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_618.
      { o0_awr. }
      o0_name HS msC. o0_post HF HFr HG EMC.
      assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 24%bv;
        25%bv; 26%bv; 27%bv] -> YK11.getr (ms_regs msC) r = YK11.getr regs' r).
      { intros r Hr. refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') msC) regs'
          [w64 (SHADOW_OFF + (l_p cx + TOP.fi_off (lo_c op) + 1) / 8); w64 sb] _ HS _ _ r Hr);
          [o0_agree E | vm_compute; reflexivity]. }
      pmkst HS. rewrite EMC, EMB, EMA in HJ |- *.
      apply (CONT (ms_regs msC) _).
      -- destruct HL as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
      -- exact KR.
Qed.

End op0.
