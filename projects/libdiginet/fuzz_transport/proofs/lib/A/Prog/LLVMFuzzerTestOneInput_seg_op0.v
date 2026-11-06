(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 594 of its 658 lines of code are new or changed and 966 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op0: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's image-A walk).
   lc_op0_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, the OP0 segment of fuzz_transport.asan's
   LLVMFuzzerTestOneInput: from the first instruction of arm 0 (+0x460, lc_st_arm cx op 0) to the call of receive
   (+0x908, lc_st_recv cx op): the inlined fuzz_record (TOps.v fuzz_record_m) and the arguments of receive.

   What the code does (offsets from 0x81264). At the arm s9 / s11 hold the cursor c before the op byte
   (p + fi_off c, fi_n c), s8 / s7 the cursor after it (p + fi_off c + 1, fi_n c - 1), s10 the shadow base.
     +0x460  `beqz s7, +0x7ec`: no byte left (fi_n c = 1): +0x7ec s11 = 0, a1 = 0, a2 = 0, `j +0x8e8`;
     +0x464  the check of the byte at s8 (shadow byte at (s8 >> 3) + s10; the slow path +0x135c goes back to +0x474
             when the shadow byte admits the access, else to the report 0x82cac), +0x474 `lbu a1, 0(s8)`, s8 = s9 + 2;
     +0x480  `bne s11, 2, +0x8c8`: one byte left (fi_n c = 2): s11 = 0, `j +0x7f4`, a2 = 0, `j +0x8e8`;
     +0x8c8  the check of the second byte (slow path +0x13d4, report 0x82ce8), +0x8d8 `lbu a2`, s11 -= 3,
             s8 = s9 + 3, a2 <<= 8;
     +0x8e8  a1 = a2 | a1 (the record's length word), `bltu a1, s11` / `mv a1, s11` (its min with the bytes left),
             s3 = s8 + a1, s7 = s11 - a1, a0 = s8, a2 = 0, a3 = 0; +0x908 is the call of receive (the cut).
   The three paths are fuzz_record_m's three cases at the cursor after the op byte (0, 1, at least 2 bytes left:
   o0_rv1, o0_rv2, o0_rv3). Each path is one run of the token engine over the walk's G journal
   (lib/A/Prog/TransportGRunA.v paj_run_to_x), two for the third path (paj_run_x to `bltu a1, s11`, the split
   paj_branch, then paj_run_to_x), from a seat whose read-only regions hold the input bytes the path reads and whose
   shadow entries cover them. The input is a heap block of the cut's blocks (lc_geom lg_in), so its shadow admits
   both checked loads (AR_laws' al_shadow through YCbq.v range_addressable_of_block): the engine takes the slow paths
   back to the loads and neither report is reached. The segment writes no byte: the memory at the cut is the arm's,
   the journal is the run's, and every other fact of lc_lcore carries over (o0_lcore_regs). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaBase DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

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

(* The arm (lo_arm 0) and the cut (LO_RECV) as offsets of the listing; the shadow base s10 is the token engine's Bx. *)
Definition O0_ARM : Z := 0x460.
Definition O0_RECV : Z := 0x908.
Definition o0_Bx : sv := SOff 26 0.
Definition o0_PTR : afact := mkAF 4096 140737479966720 0.
(* Case 1 (fi_n c = 1): no region; s7 is pinned to 0 at the seat. *)
Definition o0_ss1 : sstate := mkSS O0_ARM sr_atoms [] None (mkFacts [] [] []).
(* Case 2 (fi_n c = 2): the byte at s8 (atom 32); s7 and s11 are pinned to 1 and 2 at the seat. *)
Definition o0_rg1 : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition o0_G2 : facts :=
  mkFacts [(24%nat, o0_PTR); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] [].
Definition o0_ss2 : sstate := mkSS O0_ARM sr_atoms [o0_rg1] None o0_G2.
Definition o0_SH2 : list shent := [mkSHE 24 0 1].
(* Case 3 (fi_n c >= 3): the bytes at s8 and s9 + 2 (atoms 32, 33); s7 >= 2, s11 >= 3. *)
Definition o0_rg2 : YP09.region := YP09.mkRegion (Some 25%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 33 0))].
Definition o0_G3 : facts :=
  mkFacts [(23%nat, mkAF 2 (2 ^ 26) 0); (24%nat, o0_PTR); (25%nat, o0_PTR); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (27%nat, mkAF 3 (2 ^ 26) 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] [].
Definition o0_ss3 : sstate := mkSS O0_ARM sr_atoms [o0_rg1; o0_rg2] None o0_G3.
Definition o0_SH3 : list shent := [mkSHE 24 0 1; mkSHE 25 2 3].

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
(* The env of a seat: the registers at the arm, then the input bytes the path reads as atoms 32, 33. *)
Definition o0_E (regs : bvmap 5 word) (xs : list word) : env := Eimg (PI := PI_transport) (Ereg regs xs).
Lemma o0_E_extra : forall regs xs j, (j < 8)%nat -> ew (o0_E regs xs) (32 + j) = nth j xs (Z_to_bv 64 0).
Proof. intros regs xs j Hj. unfold o0_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
End env.

(* The value of an atom of a seat env that is a register at the arm, from the register's equation R. *)
Ltac o0_at R :=
  lazymatch type of R with YK11.getr ?rg ?r = _ =>
  lazymatch goal with |- bv_unsigned (ew _ ?n) = _ =>
    unfold o0_E; rewrite (can_ew_Eimg_Ereg_nat rg _ n r ltac:(vm_compute; reflexivity)), R; apply o0_u64 end end.

Section seat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

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

(* Case 1's seat: no region, no fact. *)
Lemma o0_seat1 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (o0_E regs []) o0_ss1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O0_ARM)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold o0_ss1.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- unfold o0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* Case 2's seat: the byte at s8 = po + 1 (atom 32). *)
Lemma o0_seat2 : forall (W : world segs) regs mem po b1,
  YK11.getr regs 24 = w64 (po + 1) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  4096 <= po + 1 <= 140737479966720 -> 0 <= b1 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (po + 1) 1 b1 ->
  st_ok_pi segs VAL (o0_E regs [w64 b1]) o0_ss2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O0_ARM)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem po b1 R24 R26 Hpo Hb1 V1.
assert (U24 : bv_unsigned (ew (o0_E regs [w64 b1]) 24) = po + 1) by (o0_at R24; lia).
assert (U26 : bv_unsigned (ew (o0_E regs [w64 b1]) 26) = SHADOW_OFF) by (o0_at R26; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew (o0_E regs [w64 b1]) 32) = b1)
  by (pose proof (o0_E_extra regs [w64 b1] 0 ltac:(lia)) as H; cbn [Nat.add nth] in H; rewrite H; apply o0_u64; lia).
rewrite restrict_mkst_fx. unfold o0_ss2.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- unfold o0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, o0_rg1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs _ _ (po + 1) 0 1 (SOff 32 0) b1);
    [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V1].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, o0_rg1.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. exact (conj I I).
- unfold o0_G2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, o0_PTR. cbn [af_lo af_hi af_al2]. rewrite U24, U26, U32.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* Case 3's seat: the bytes at s8 = po + 1 and s9 + 2 = po + 2 (atoms 32, 33); s7 = n - 1, s11 = n. *)
Lemma o0_seat3 : forall (W : world segs) regs mem po n b1 b2,
  YK11.getr regs 23 = w64 (n - 1) -> YK11.getr regs 24 = w64 (po + 1) -> YK11.getr regs 25 = w64 po ->
  YK11.getr regs 26 = w64 SHADOW_OFF -> YK11.getr regs 27 = w64 n ->
  3 <= n <= 2 ^ 26 -> 4096 <= po -> po + 3 <= 140737479966720 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (po + 1) 1 b1 -> val_mem segs (mrestrict (w_H W) mem) (po + 2) 1 b2 ->
  st_ok_pi segs VAL (o0_E regs [w64 b1; w64 b2]) o0_ss3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O0_ARM)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem po n b1 b2 R23 R24 R25 R26 R27 Hn Hlo Hhi Hb1 Hb2 V1 V2.
assert (U23 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 23) = n - 1) by (o0_at R23; lia).
assert (U24 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 24) = po + 1) by (o0_at R24; lia).
assert (U25 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 25) = po) by (o0_at R25; lia).
assert (U26 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 26) = SHADOW_OFF) by (o0_at R26; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 27) = n) by (o0_at R27; lia).
assert (U32 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 32) = b1)
  by (pose proof (o0_E_extra regs [w64 b1; w64 b2] 0 ltac:(lia)) as H; cbn [Nat.add nth] in H; rewrite H;
      apply o0_u64; lia).
assert (U33 : bv_unsigned (ew (o0_E regs [w64 b1; w64 b2]) 33) = b2)
  by (pose proof (o0_E_extra regs [w64 b1; w64 b2] 1 ltac:(lia)) as H; cbn [Nat.add nth] in H; rewrite H;
      apply o0_u64; lia).
rewrite restrict_mkst_fx. unfold o0_ss3.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- unfold o0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, o0_rg1.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ (po + 1) 0 1 (SOff 32 0) b1);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V1].
  + unfold region_ok, o0_rg2.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U25.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ po 2 1 (SOff 33 0) b2);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact V2].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, o0_rg1, o0_rg2.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U25.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold o0_G3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, o0_PTR. cbn [af_lo af_hi af_al2]. rewrite U23, U24, U25, U26, U27, U32, U33.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

End seat.

(* ------------------------------------------------------------------ *)
(* 3. The engine's helpers                                              *)
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

(* ------------------------------------------------------------------ *)
(* 4. The segment                                                       *)
(* ------------------------------------------------------------------ *)

Section op0. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* lc_lcore holds of any registers that agree on the ones it names (sp, gp, tp, s0, s1, s2, s5, s10). *)
Lemma o0_lcore_regs : forall cx op k ly S (W : world segs) regs mem md e regs2,
  lc_lcore B MT cx op false false k ly S W regs mem md e ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 26%bv] -> YK11.getr regs2 r = YK11.getr regs r) ->
  lc_lcore B MT cx op false false k ly S W regs2 mem md e.
Proof.
intros cx op k ly S W regs mem md e regs2 HL RR.
destruct HL as (HC & (F18 & F26) & HSP & HFSH & HOK & HE & HM & R21).
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
- exact (eq_trans (RR 21%bv ltac:(cbn; tauto)) R21).
Qed.

(* The cut from the facts the runs leave. *)
Lemma o0_close : forall cx op ly S (W : world segs) mem md e regs2 rv,
  lc_lcore B MT cx op false false (lo_k op) ly S W regs2 mem md e ->
  lc_tw W mem (lo_B op) ->
  lc_opc (l_pl cx) (lo_c op) = 0 ->
  lc_recv_vals (l_pl cx) (lo_c op) = rv ->
  YK11.getr regs2 10 = w64 (l_p cx + rv_off rv) -> YK11.getr regs2 11 = w64 (rv_n rv) ->
  YK11.getr regs2 12 = w64 (rv_bp rv) -> YK11.getr regs2 13 = w64 (rv_pf rv) ->
  YK11.getr regs2 19 = w64 (l_p cx + TOP.fi_off (rv_c rv)) -> YK11.getr regs2 23 = w64 (TOP.fi_n (rv_c rv)) ->
  YK11.getr regs2 20 = w64 LF_S4 -> YK11.getr regs2 22 = w64 7 ->
  lc_st_recv B MT cx op W (lc_cfg cx LO_RECV regs2 mem md).
Proof.
intros cx op ly S W mem md e regs2 rv HL Htw Ho Erv R10 R11 R12 R13 R19 R23 R20 R22.
exists ly, S, regs2, mem, md, e. cbv zeta. rewrite Erv.
split; [reflexivity|]. split; [left; exact Ho|]. split; [exact HL|]. split; [exact Htw|].
split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
split; [split; [exact R19 | exact R23]|]. split; [exact R20 | exact R22].
Qed.

Lemma lc_op0_ok : lc_op0_stmt B MT XL RLO RHI.
Proof.
unfold lc_op0_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & -> & Ho & HL & Htw & Hc0 & Hc1 & R20 & R22).
symmetry in Ho.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HL as (HC & (R18 & R26) & _ & _ & (_ & _ & HCok & Hn0 & _) & _).
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HPAY & _)).
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as [HAR _ _ _ _ _ (Hln & Hlen) HIN _].
destruct HCok as (Hoff & Hn & Hsum).
rewrite (o0_oc (l_pl cx) (lo_c op) Hn0) in Hc1.
destruct Hc0 as (R25 & R27). destruct Hc1 as (R24 & R23). cbn [TOP.fi_off TOP.fi_n] in R24, R23.
assert (Hin : In (l_p cx, l_n cx) (ablocks B ly' S')) by (apply HIN; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4 & Hpc & _).
pose proof (req_size_pos (l_n cx) ltac:(lia)) as [Hq1 Hq2].
pose proof (@alloc_ceiling_value rc) as ((_ & Hceil) & _).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
change (SRr segs W' (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + O0_ARM)) mem' (YK11.seg_rom segs)) md')
  (lc_st_recv B MT cx op)).
rewrite Z.add_assoc in R24.
destruct (Z.eq_dec (TOP.fi_n (lo_c op)) 1) as [E1 | E1];
  [| destruct (Z.eq_dec (TOP.fi_n (lo_c op)) 2) as [E2 | E2]].
- (* fi_n c = 1: no byte after the op byte; s7 = 0 *)
  set (E := o0_E regs' []).
  pose proof (@o0_seat1 (l_fx cx) rc W' regs' mem') as HS0. fold E in HS0.
  pose proof (st_ok_pi_pin_reg' E o0_ss1 _ 23%bv 0 HS0
    ltac:(cbn [ms_regs restrict YK11.mkst]; rewrite E1 in R23; exact R23) eq_refl) as HS.
  clear HS0.
  assert (SHOK : sh_ok segs o0_Bx [] E (mrestrict (w_H W') mem')) by constructor.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, o0_E; apply Eimg_env).
  assert (A24 : bv_unsigned (ew E 24) = l_p cx + TOP.fi_off (lo_c op) + 1) by (unfold E; o0_at R24; lia).
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_RECV.
  { o0_awr. }
  set (md1 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md1. clear mat.
  assert (EM : ms_mem ms = mem') by (o0_mem HF).
  clear HF HFr HG.
  (* +0x908: a0 = s3 = s8, a1 = a2 = a3 = s7 = 0 *)
  o0_rd HS (10%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 1))) X10 o0_rval.
  o0_rd HS (11%bv : bv 5) (w64 0) X11 o0_rval.
  o0_rd HS (12%bv : bv 5) (w64 0) X12 o0_rval.
  o0_rd HS (13%bv : bv 5) (w64 0) X13 o0_rval.
  o0_rd HS (19%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 1))) X19 o0_rval.
  o0_rd HS (23%bv : bv 5) (w64 0) X23 o0_rval.
  assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
    YK11.getr (ms_regs ms) r = YK11.getr regs' r).
  { intros r Hr. refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') ms) regs' [] _ HS _ _ r Hr);
      [o0_agree E | vm_compute; reflexivity]. }
  pmkst HS. apply SRr_ret. rewrite EM in HJ |- *.
  apply (o0_close cx op ly' S' W' mem' md1 e (ms_regs ms)
    (mkLrv 0 0 (TOP.fi_off (lo_c op) + 1) 0 (TOP.FuzzIn (TOP.fi_off (lo_c op) + 1) 0))).
  + apply (o0_lcore_regs cx op (lo_k op) ly' S' W' regs' mem' md1 e (ms_regs ms)).
    * destruct HL as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
    * intros r Hr. apply KR. cbn in Hr |- *. tauto.
  + exact Htw.
  + exact Ho.
  + exact (o0_rv1 (l_pl cx) (lo_c op) E1 Ho).
  + exact X10.
  + exact X11.
  + exact X12.
  + exact X13.
  + exact X19.
  + exact X23.
  + exact (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20).
  + exact (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22).
- (* fi_n c = 2: one byte after the op byte *)
  remember (DSpec.at8 (l_pl cx) (Z.to_nat (TOP.fi_off (lo_c op) + 1))) as b1 eqn:Eb1.
  assert (Hb1 : 0 <= b1 < 256) by (rewrite Eb1; apply o0_at8).
  assert (V1 : val_mem segs (mrestrict (w_H W') mem') (l_p cx + TOP.fi_off (lo_c op) + 1) 1 b1).
  { rewrite Eb1, <- Z.add_assoc.
    exact (o0_inbyte (w_H W') mem' (l_p cx) (l_pl cx) (TOP.fi_off (lo_c op) + 1) HPAY ltac:(lia)). }
  set (E := o0_E regs' [w64 b1]).
  pose proof (@o0_seat2 (l_fx cx) rc W' regs' mem' (l_p cx + TOP.fi_off (lo_c op)) b1 R24 R26 ltac:(lia) Hb1 V1)
    as HS0. fold E in HS0.
  pose proof (st_ok_pi_pin_reg' E o0_ss2 _ 23%bv 1 HS0
    ltac:(cbn [ms_regs restrict YK11.mkst]; rewrite E2 in R23; exact R23) eq_refl) as HS1.
  pose proof (st_ok_pi_pin_reg' E _ _ 27%bv 2 HS1
    ltac:(cbn [ms_regs restrict YK11.mkst]; rewrite E2 in R27; exact R27) eq_refl) as HS.
  clear HS0 HS1.
  assert (A24 : bv_unsigned (ew E 24) = l_p cx + TOP.fi_off (lo_c op) + 1) by (unfold E; o0_at R24; lia).
  assert (A25 : bv_unsigned (ew E 25) = l_p cx + TOP.fi_off (lo_c op)) by (unfold E; o0_at R25; lia).
  assert (A26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (unfold E; o0_at R26; unfold SHADOW_OFF; lia).
  assert (A32 : bv_unsigned (ew E 32) = b1)
    by (unfold E; pose proof (o0_E_extra regs' [w64 b1] 0 ltac:(lia)) as H; cbn [Nat.add nth] in H; rewrite H;
        apply o0_u64; lia).
  assert (SHOK : sh_ok segs o0_Bx o0_SH2 E (mrestrict (w_H W') mem')).
  { unfold sh_ok, o0_SH2. apply Forall_cons; [|apply Forall_nil].
    apply (o0_sh B LAWS E W' mem' ly' S' md' (l_p cx) (l_n cx) 24 (l_p cx + TOP.fi_off (lo_c op) + 1) 0 1 HAR Hin);
      [ lia
      | unfold o0_Bx; rewrite (o0_U_off E 26 0 SHADOW_OFF A26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (o0_U_off E 24 0 _ A24) by lia; apply Z.add_0_r
      | lia | lia | lia ]. }
  assert (HEI : img_env VAL A_LIM E) by (unfold E, o0_E; apply Eimg_env).
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_RECV.
  { o0_awr. }
  set (md1 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md1. clear mat.
  assert (EM : ms_mem ms = mem') by (o0_mem HF).
  clear HF HFr HG.
  (* +0x908: a0 = s3 = s9 + 2, a1 = a2 = a3 = s7 = 0 *)
  o0_rd HS (10%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 2))) X10 o0_rval.
  o0_rd HS (11%bv : bv 5) (w64 0) X11 o0_rval.
  o0_rd HS (12%bv : bv 5) (w64 0) X12 o0_rval.
  o0_rd HS (13%bv : bv 5) (w64 0) X13 o0_rval.
  o0_rd HS (19%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 2))) X19 o0_rval.
  o0_rd HS (23%bv : bv 5) (w64 0) X23 o0_rval.
  assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
    YK11.getr (ms_regs ms) r = YK11.getr regs' r).
  { intros r Hr. refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') ms) regs' [w64 b1] _ HS _ _ r Hr);
      [o0_agree E | vm_compute; reflexivity]. }
  pmkst HS. apply SRr_ret. rewrite EM in HJ |- *.
  apply (o0_close cx op ly' S' W' mem' md1 e (ms_regs ms)
    (mkLrv 0 0 (TOP.fi_off (lo_c op) + 2) 0 (TOP.FuzzIn (TOP.fi_off (lo_c op) + 2) 0))).
  + apply (o0_lcore_regs cx op (lo_k op) ly' S' W' regs' mem' md1 e (ms_regs ms)).
    * destruct HL as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
    * intros r Hr. apply KR. cbn in Hr |- *. tauto.
  + exact Htw.
  + exact Ho.
  + exact (o0_rv2 (l_pl cx) (lo_c op) E2 Ho).
  + exact X10.
  + exact X11.
  + exact X12.
  + exact X13.
  + exact X19.
  + exact X23.
  + exact (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20).
  + exact (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22).
- (* fi_n c >= 3: two bytes after the op byte *)
  assert (Hn3 : 3 <= TOP.fi_n (lo_c op)) by lia.
  remember (DSpec.at8 (l_pl cx) (Z.to_nat (TOP.fi_off (lo_c op) + 1))) as b1 eqn:Eb1.
  remember (DSpec.at8 (l_pl cx) (Z.to_nat (TOP.fi_off (lo_c op) + 2))) as b2 eqn:Eb2.
  assert (Hb1 : 0 <= b1 < 256) by (rewrite Eb1; apply o0_at8).
  assert (Hb2 : 0 <= b2 < 256) by (rewrite Eb2; apply o0_at8).
  assert (V1 : val_mem segs (mrestrict (w_H W') mem') (l_p cx + TOP.fi_off (lo_c op) + 1) 1 b1).
  { rewrite Eb1, <- Z.add_assoc.
    exact (o0_inbyte (w_H W') mem' (l_p cx) (l_pl cx) (TOP.fi_off (lo_c op) + 1) HPAY ltac:(lia)). }
  assert (V2 : val_mem segs (mrestrict (w_H W') mem') (l_p cx + TOP.fi_off (lo_c op) + 2) 1 b2).
  { rewrite Eb2, <- Z.add_assoc.
    exact (o0_inbyte (w_H W') mem' (l_p cx) (l_pl cx) (TOP.fi_off (lo_c op) + 2) HPAY ltac:(lia)). }
  set (E := o0_E regs' [w64 b1; w64 b2]).
  pose proof (@o0_seat3 (l_fx cx) rc W' regs' mem' (l_p cx + TOP.fi_off (lo_c op)) (TOP.fi_n (lo_c op)) b1 b2
    R23 R24 R25 R26 R27 ltac:(lia) ltac:(lia) ltac:(lia) Hb1 Hb2 V1 V2) as HS. fold E in HS.
  assert (A23 : bv_unsigned (ew E 23) = TOP.fi_n (lo_c op) - 1) by (unfold E; o0_at R23; lia).
  assert (A24 : bv_unsigned (ew E 24) = l_p cx + TOP.fi_off (lo_c op) + 1) by (unfold E; o0_at R24; lia).
  assert (A25 : bv_unsigned (ew E 25) = l_p cx + TOP.fi_off (lo_c op)) by (unfold E; o0_at R25; lia).
  assert (A26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (unfold E; o0_at R26; unfold SHADOW_OFF; lia).
  assert (A27 : bv_unsigned (ew E 27) = TOP.fi_n (lo_c op)) by (unfold E; o0_at R27; lia).
  assert (A32 : bv_unsigned (ew E 32) = b1)
    by (unfold E; pose proof (o0_E_extra regs' [w64 b1; w64 b2] 0 ltac:(lia)) as H; cbn [Nat.add nth] in H;
        rewrite H; apply o0_u64; lia).
  assert (A33 : bv_unsigned (ew E 33) = b2)
    by (unfold E; pose proof (o0_E_extra regs' [w64 b1; w64 b2] 1 ltac:(lia)) as H; cbn [Nat.add nth] in H;
        rewrite H; apply o0_u64; lia).
  assert (SHOK : sh_ok segs o0_Bx o0_SH3 E (mrestrict (w_H W') mem')).
  { unfold sh_ok, o0_SH3. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (o0_sh B LAWS E W' mem' ly' S' md' (l_p cx) (l_n cx) 24 (l_p cx + TOP.fi_off (lo_c op) + 1) 0 1
        HAR Hin);
        [ lia
        | unfold o0_Bx; rewrite (o0_U_off E 26 0 SHADOW_OFF A26) by (unfold SHADOW_OFF; lia); reflexivity
        | rewrite (o0_U_off E 24 0 _ A24) by lia; apply Z.add_0_r
        | lia | lia | lia ].
    - apply (o0_sh B LAWS E W' mem' ly' S' md' (l_p cx) (l_n cx) 25 (l_p cx + TOP.fi_off (lo_c op)) 2 3 HAR Hin);
        [ lia
        | unfold o0_Bx; rewrite (o0_U_off E 26 0 SHADOW_OFF A26) by (unfold SHADOW_OFF; lia); reflexivity
        | rewrite (o0_U_off E 25 0 _ A25) by lia; apply Z.add_0_r
        | lia | lia | lia ]. }
  assert (HEI : img_env VAL A_LIM E) by (unfold E, o0_E; apply Eimg_env).
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { o0_awr. }
  set (md1 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md1. clear mat.
  assert (EM : ms_mem ms = mem') by (o0_mem HF).
  clear HF HFr HG.
  (* +0x8ec: `bltu a1, s11`, a1 = the length word, s11 = the bytes left after it *)
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
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_RECV.
    { o0_awr. }
    set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
    assert (EM2 : ms_mem ms0 = ms_mem ms) by (o0_mem HF).
    clear HF HFr HG.
    (* +0x908: a0 = s9 + 3, a1 = the length word, s3 = s8 + a1, s7 = s11 - a1, a2 = a3 = 0 *)
    o0_rd HS (10%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 3))) X10 o0_rval.
    o0_rd HS (11%bv : bv 5) (w64 (b1 + 256 * b2)) X11 o0_rval.
    o0_rd HS (12%bv : bv 5) (w64 0) X12 o0_rval.
    o0_rd HS (13%bv : bv 5) (w64 0) X13 o0_rval.
    o0_rd HS (19%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 3 + (b1 + 256 * b2)))) X19 o0_rval.
    o0_rd HS (23%bv : bv 5) (w64 (TOP.fi_n (lo_c op) - 3 - (b1 + 256 * b2))) X23 o0_rval.
    assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
      YK11.getr (ms_regs ms0) r = YK11.getr regs' r).
    { intros r Hr. refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') ms0) regs' [w64 b1; w64 b2] _ HS _ _ r Hr);
        [o0_agree E | vm_compute; reflexivity]. }
    pmkst HS. apply SRr_ret. rewrite EM2, EM in HJ |- *.
    apply (o0_close cx op ly' S' W' mem' md2 e (ms_regs ms0)
      (mkLrv 0 0 (TOP.fi_off (lo_c op) + 3) (b1 + 256 * b2)
         (TOP.FuzzIn (TOP.fi_off (lo_c op) + 3 + (b1 + 256 * b2)) (TOP.fi_n (lo_c op) - 3 - (b1 + 256 * b2))))).
    * apply (o0_lcore_regs cx op (lo_k op) ly' S' W' regs' mem' md2 e (ms_regs ms0)).
      -- destruct HL as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
      -- intros r Hr. apply KR. cbn in Hr |- *. tauto.
    * exact Htw.
    * exact Ho.
    * rewrite (o0_rv3 (l_pl cx) (lo_c op) Hn3 Ho), EL. reflexivity.
    * exact X10.
    * exact X11.
    * exact X12.
    * exact X13.
    * exact X19.
    * exact X23.
    * exact (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20).
    * exact (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22).
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
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O0_RECV.
    { o0_awr. }
    set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
    assert (EM2 : ms_mem ms0 = ms_mem ms) by (o0_mem HF).
    clear HF HFr HG.
    (* +0x908: a0 = s9 + 3, a1 = s11 = the bytes left, s3 = s8 + a1, s7 = 0, a2 = a3 = 0 *)
    o0_rd HS (10%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 3))) X10 o0_rval.
    o0_rd HS (11%bv : bv 5) (w64 (TOP.fi_n (lo_c op) - 3)) X11 o0_rval.
    o0_rd HS (12%bv : bv 5) (w64 0) X12 o0_rval.
    o0_rd HS (13%bv : bv 5) (w64 0) X13 o0_rval.
    o0_rd HS (19%bv : bv 5) (w64 (l_p cx + (TOP.fi_off (lo_c op) + 3 + (TOP.fi_n (lo_c op) - 3)))) X19 o0_rval.
    o0_rd HS (23%bv : bv 5) (w64 (TOP.fi_n (lo_c op) - 3 - (TOP.fi_n (lo_c op) - 3))) X23 o0_rval.
    assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
      YK11.getr (ms_regs ms0) r = YK11.getr regs' r).
    { intros r Hr. refine (regs_kept_of_st_ok_pi _ _ (restrict (w_H W') ms0) regs' [w64 b1; w64 b2] _ HS _ _ r Hr);
        [o0_agree E | vm_compute; reflexivity]. }
    pmkst HS. apply SRr_ret. rewrite EM2, EM in HJ |- *.
    apply (o0_close cx op ly' S' W' mem' md2 e (ms_regs ms0)
      (mkLrv 0 0 (TOP.fi_off (lo_c op) + 3) (TOP.fi_n (lo_c op) - 3)
         (TOP.FuzzIn (TOP.fi_off (lo_c op) + 3 + (TOP.fi_n (lo_c op) - 3))
                     (TOP.fi_n (lo_c op) - 3 - (TOP.fi_n (lo_c op) - 3))))).
    * apply (o0_lcore_regs cx op (lo_k op) ly' S' W' regs' mem' md2 e (ms_regs ms0)).
      -- destruct HL as (HC0 & HL0). destruct HC0 as (_ & HC1). exact (conj (conj HJ HC1) HL0).
      -- intros r Hr. apply KR. cbn in Hr |- *. tauto.
    * exact Htw.
    * exact Ho.
    * rewrite (o0_rv3 (l_pl cx) (lo_c op) Hn3 Ho), EL. reflexivity.
    * exact X10.
    * exact X11.
    * exact X12.
    * exact X13.
    * exact X19.
    * exact X23.
    * exact (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20).
    * exact (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22).
Qed.

End op0.
