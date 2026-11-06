(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_cmp_defs: the symbolic states, the atom numbering and the C-level index facts of
   the image-B cmp segment (lib/B/Prog/LLVMFuzzerTestOneInput_segF.v, llvm_b_cmp_stmt, +0x6f0 .. +0x83c).
   The shape is a Theorem Labs lane's walk of record (a working branch, lib/A/Prog/GrantEntrySweepS2.v: a symbolic state
   per cut, the shadow band as an atom, one shadow entry per access, the loop by induction on what is left), and
   cgif_file_fuzzer's lib/A/ACf5.v (rt_regions0 / rt_atoms0 / RTBspan) for the atom-fact shapes.

   The atoms this segment fixes (registers keep atoms 0..31; A_TEXT = 240 upwards is the image, PaTable.v:13-15):
     32  the shadow base SHADOW_OFF, i.e. Bx          (32(s1), loaded into a7 at +0x714)
     33  out, the decode buffer                       (88(s1))
     34  res, the payload copy                        (40(s1))
     35  len = dec_b_len n                            (24(s1))
     36  ns mod 2 ^ 64                                (72(s1))
     37  nch mod 2 ^ 32                               (64(s1))
     38  ns mod 2 ^ 32                                (56(s1))
     39  res + 50                                     (80(s1))
     40  the fake frame d_F                           (0(s1), 16(s1), 112(s1))
     41  its shadow address d_SH                      (8(s1))
     44  the one byte the scan loop L2 reads          (out + i)
   The spill area at s1 is one region: read-only but for 48(s1), the one slot this segment stores (3 * ns at
   +0x7bc, read back at +0x814; a Theorem Labs lane's measurement on DecodeBList, 2026-10-29). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_decode_plain_le_c reac_frame_inspect_c.
Import ListNotations.
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_c.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_inspect_c.

(* ------------------------------------------------------------------ *)
(* 1. The C-level index fact the bcmp double loop needs                 *)
(* ------------------------------------------------------------------ *)

(* plain_out is the de-interleaving of the payload: byte 3 * (j * ns + k) + r of the decoder's output is byte
   50 + 3 * (k * nch + j) + r of the frame (reac_decode_plain_le_c.v:15-19 plain_byte / plain_out).  The double
   loop L3/L4 at +0x7c0..+0x820 compares exactly those two triples, channel j against sample k, so every bcmp
   finds them equal and the mismatch edge at +0x82c is refuted. *)
Lemma cm_plain_len : forall bs nch ns,
  length (CPlain.plain_out bs nch ns) = Z.to_nat (3 * nch * ns).
Proof.
intros bs nch ns. unfold CPlain.plain_out. rewrite !length_map, length_seq. reflexivity.
Qed.

Lemma cm_nth_plain : forall bs nch ns i,
  0 <= i < 3 * nch * ns ->
  nth (Z.to_nat i) (CPlain.plain_out bs nch ns) (Z_to_bv 8 0) = CPlain.plain_byte bs nch ns i.
Proof.
intros bs nch ns i Hi. unfold CPlain.plain_out. rewrite map_map.
rewrite (nth_indep _ (Z_to_bv 8 0) (CPlain.plain_byte bs nch ns (Z.of_nat 0%nat)))
  by (rewrite length_map, length_seq; lia).
rewrite (map_nth (fun k : nat => CPlain.plain_byte bs nch ns (Z.of_nat k))
           (seq 0 (Z.to_nat (3 * nch * ns))) 0%nat).
rewrite seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma cm_idx : forall (ns j k r : Z),
  0 < ns -> 0 <= j -> 0 <= k < ns -> 0 <= r < 3 ->
  (3 * (j * ns + k) + r) / 3 = j * ns + k /\ (3 * (j * ns + k) + r) mod 3 = r.
Proof.
intros ns j k r Hns Hj Hk Hr.
split.
- rewrite Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small r 3) by lia. lia.
- rewrite Z.mul_comm, Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma cm_plain_byte_at : forall bs nch ns j k r,
  0 < nch -> 0 < ns -> 0 <= j < nch -> 0 <= k < ns -> 0 <= r < 3 ->
  CPlain.plain_byte bs nch ns (3 * (j * ns + k) + r)
  = nth (Z.to_nat (50 + 3 * (k * nch + j) + r)) bs (Z_to_bv 8 0).
Proof.
intros bs nch ns j k r Hnch Hns Hj Hk Hr.
unfold CPlain.plain_byte.
destruct (cm_idx ns j k r Hns ltac:(lia) Hk Hr) as [Hd Hm].
rewrite Hd, Hm.
replace ((j * ns + k) mod ns) with k
  by (symmetry; rewrite Z.add_comm, Z_mod_plus_full; apply Z.mod_small; lia).
replace ((j * ns + k) / ns) with j
  by (symmetry; rewrite Z.add_comm, Z.div_add by lia; rewrite (Z.div_small k ns) by lia; lia).
reflexivity.
Qed.

(* The two indices stay inside the two buffers: the output has 3 * nch * ns bytes and plain_ok pins the frame at
   1492 bytes (reac_frame_inspect_c.v:13-15 inspect_wf) with nch * ns <= 480, so 50 + 3 * nch * ns <= 1490. *)
Lemma cm_plain_ok_facts : forall len bs nch ns,
  CPlain.plain_ok len bs nch ns = true -> len = 1492 /\ 0 < nch /\ 0 < ns /\ nch * ns <= 480.
Proof.
intros len bs nch ns H. unfold CPlain.plain_ok in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H4. apply Z.ltb_lt in H3. apply Z.ltb_lt in H2.
unfold CInsp.inspect_wf in H1.
apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1 _].
apply andb_prop in H1 as [H1 _]. apply Z.eqb_eq in H1.
split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

(* The plain-result check at +0x6fc: `bne a0, (s3 - 1) | ns` with a0 = plain_ok ? ns : -1 and
   s3 = plain_ok ? 1 : 0 (llvm_b_st_6f0), so the two sides agree and the abort edge into +0xb88 is refuted. *)
Lemma cm_bits_hi : forall y i, 0 <= y < 2 ^ 64 -> 64 <= i -> Z.testbit y i = false.
Proof.
intros y i Hy Hi. destruct (Z.eq_dec y 0) as [->|Hn]; [apply Z.testbit_0_l|].
assert (Hpos : 0 < y) by lia.
assert (HL : Z.log2 y < 64)
  by (first [apply (proj2 (Z.log2_lt_pow2 y 64 Hpos)) | apply (proj1 (Z.log2_lt_pow2 y 64 Hpos))]; lia).
apply Z.bits_above_log2; lia.
Qed.

Lemma cm_lor_ones : forall y, 0 <= y < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) y = 2 ^ 64 - 1.
Proof.
intros y Hy.
assert (E : 2 ^ 64 - 1 = Z.ones 64) by (rewrite Z.ones_equiv; lia).
rewrite E. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z_lt_le_dec i 64) as [Hlt|Hge].
- rewrite Z.ones_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite (cm_bits_hi y i Hy Hge). reflexivity.
Qed.

Lemma cm_or_check : forall (p : bool) (ns : Z),
  Z.lor (((if p then 1 else 0) - 1) mod 2 ^ 64) (ns mod 2 ^ 64)
  = (if p then ns else -1) mod 2 ^ 64.
Proof.
intros p ns. assert (HM : (-1) mod 2 ^ 64 = 2 ^ 64 - 1) by reflexivity.
destruct p; cbn [negb].
- replace ((1 - 1) mod 2 ^ 64) with 0 by reflexivity. rewrite Z.lor_0_l. reflexivity.
- replace ((0 - 1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  rewrite cm_lor_ones by (apply Z.mod_pos_bound; lia). symmetry. exact HM.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                               *)
(* ------------------------------------------------------------------ *)

Definition cm_Bx : sv := SOff 32 0.
Definition cm_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* alloc_ceiling is a field of the run's RunCeil (lib/Reusable/YM05.v:17-19), between CEIL_MIN and CEIL_MAX, so an
   atom fact that vm_compute must see needs the literal bounds: a heap pointer is below CEIL_MAX (YC4b.v:27 PTR)
   and the realigned stack is above CEIL_MIN. *)
Definition CM_BLK_HI : Z := 0x7fffff800000.
Definition CM_SP_LO : Z := 0x7fff7f800000.

(* The spill area at s1 (atom 9).  Every slot llvm_b_st_6f0 states, plus the three of dec_b_frs; 48(s1) carries
   no chunk at the cut, because the segment writes it before it reads it (+0x7bc / +0x814). *)
Definition cm_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 48 56
    [ YP09.mkChunk 0 (CVal 8 (SOff 40 0));
      YP09.mkChunk 8 (CVal 8 (SOff 41 0));
      YP09.mkChunk 16 (CVal 8 (SOff 40 0));
      YP09.mkChunk 24 (CVal 8 (SOff 35 0));
      YP09.mkChunk 32 (CVal 8 (SOff 32 0));
      YP09.mkChunk 40 (CVal 8 (SOff 34 0));
      YP09.mkChunk 56 (CVal 8 (SOff 38 0));
      YP09.mkChunk 64 (CVal 8 (SOff 37 0));
      YP09.mkChunk 72 (CVal 8 (SOff 36 0));
      YP09.mkChunk 80 (CVal 8 (SOff 39 0));
      YP09.mkChunk 88 (CVal 8 (SOff 33 0));
      YP09.mkChunk 112 (CVal 8 (SOff 40 0)) ].

(* The facts the engine reads: the shadow base, the realigned stack's 32-alignment, and the two heap pointers below
   CEIL_MAX (the +0x774 guard `bltu -51, res` is discharged from atom 34's). *)
Definition cm_atoms0 : list (nat * afact) :=
  [ (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (9%nat, mkAF CM_SP_LO (2 ^ 47) 5);
    (33%nat, mkAF 4096 CM_BLK_HI 0);
    (34%nat, mkAF 4096 CM_BLK_HI 0) ].
Definition cm_facts0 : facts := mkFacts cm_atoms0 [] [].
Definition ss_cm_6f0 : sstate := mkSS 0x6f0 sr_atoms [cm_spill] None cm_facts0.

(* The slots the segment's loops read (24 .. 88 but 48), read-only: the loops write no memory. *)
Definition cm_spill_chunks : list YP09.chunk :=
  [ YP09.mkChunk 24 (CVal 8 (SOff 35 0));
    YP09.mkChunk 32 (CVal 8 (SOff 32 0));
    YP09.mkChunk 40 (CVal 8 (SOff 34 0));
    YP09.mkChunk 56 (CVal 8 (SOff 38 0));
    YP09.mkChunk 64 (CVal 8 (SOff 37 0));
    YP09.mkChunk 72 (CVal 8 (SOff 36 0));
    YP09.mkChunk 80 (CVal 8 (SOff 39 0));
    YP09.mkChunk 88 (CVal 8 (SOff 33 0)) ].

(* The scan loop L2 (+0x718 .. +0x748, the refused-decode path): the spill slots, and the one byte the turn reads,
   out + i (atom 44, the engine's alias of `add a1, a1, a3` with a1 = out, a3 = i), which holds the 0xa5 fill. The
   shadow base is a7 (+0x714), so atom 17 is Bx; the shadow entry says out + i is addressable. *)
Definition cm_spillL2 : YP09.region := YP09.mkRegion (Some 9%nat) 0 120 0 0 cm_spill_chunks.
Definition cm_byte44 : YP09.region := YP09.mkRegion (Some 44%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 165))].
Definition cm_factsL2 : facts :=
  mkFacts [ (17%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (9%nat, mkAF CM_SP_LO (2 ^ 47) 5);
            (33%nat, mkAF 4096 CM_BLK_HI 0);
            (44%nat, mkAF 4096 CM_BLK_HI 0) ] []
          [(SAlu ALU_ADD (SOff 33 0) (SOff 13 0), SOff 44 0)].
Definition cm_ssL2 : sstate := mkSS 0x718 sr_atoms [cm_spillL2; cm_byte44] None cm_factsL2.
Definition cm_BxL2 : sv := SOff 17 0.
Definition cm_SHL2 : list shent := [mkSHE 44 0 1].

(* The bcmp loops L3 / L4 (+0x7c0 .. +0x830, the accepted-decode path): the spill slots and 48(s1) = 3 * ns (atom 45),
   which +0x7bc stored before the loops. bcmp does its own shadow checks, so there is no shadow entry. *)
Definition cm_spillL : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 0 0 (YP09.mkChunk 48 (CVal 8 (SOff 45 0)) :: cm_spill_chunks).
Definition cm_ssL (pc : Z) : sstate := mkSS pc sr_atoms [cm_spillL] None cm_facts0.
