(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEdge), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACgb.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEdge.v at a working branch af735a950e2 (blob 4872b8584d0; the walk was ported from blob cc682d0a16f at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; image B divides the index by 3 with mulhu where image A uses zext8(i)*171>>9, and adds UBSan traps T3..T11 *)
(* The edge scan of reac_headamp_tx_next on the ASan+UBSan build (fuzz_grant.asan-ubsan, the slot
   LOOPD 0x85fb8 of lib/B/Prog/HeadampTxNext.v). The scan runs over the 144 flattened cells of the
   table's dirty array at offset 288: at each index it reads the dirty byte; at the first non-zero
   one it clears that byte, writes the channel i / 3, the parameter i mod 3 and the value tb T i into
   the three bytes the caller holds, clears resweep_wait at 456 and returns 1 through the epilogue
   0x862cc; if no cell is dirty the scan falls out at AFTR 0x86100.

   Where image B differs from image A (0x8514c) and how this file meets it:
   - the index is held five times (a7 and a4 as i, a0 as tx + i, t2 as 288 + i, t1 as the 32-bit
     count i - 144), the table is s0 (atom 8), the value pointer s1 (atom 9), the channel and
     parameter pointers a1 and a2 (atoms 11, 12), and the shadow base s5 (pinned to atom 32);
   - the code divides by 3 twice, by two different mulhu reciprocals:
       c = mulhu(i << 32, 0xAAAAAAAB << 32) >> 33   and   c = mulhu(i, 0xAAAAAAAAAAAAAAAB) >> 1,
       p = i - ((mulhu(i, 0xAAAAAAAAAAAAAAAB) & -2) + c);
     the aliases of nd_alias name those trees by atoms 51 (c), 54 (p), 55 and 56, and nd_UQ1 /
     nd_UQ2 / nd_UAND prove the three mulhu identities for 0 <= i < 144 by evaluating all 144 cases;
   - the frame is 96 bytes and the epilogue reads back ra and s0..s10 (atoms 60..71);
   - the nine UBSan guards of this segment all jump to the one `unimp` at 0x8644c and none is taken:
       0x85fd0 (tx + 288 + 3c wraps) and 0x85ff0 (tx + 288 + 3c + p wraps): decided from the ranges
       of atoms 53 / 51 and 55 / 54;
       0x8604c (chp = 0), 0x86064 (parp = 0), 0x860b4 (valp = 0): atoms 11, 12, 9 are >= 4096;
       0x860a4 (tx + 3c = 0), 0x860ac (tx + i = 0): the ranges of tx + 3c and atom 48 start at 4096;
       0x860a8 (tx + 3c wraps below tx) and 0x860b0 (tx + i below tx + 3c): the two conditions of
       nd_conds, proved at the seat from 0 <= 3c <= i < 144;
   - the seven instrumented accesses of the segment (analysis rows 3..9: the dirty byte's load and
     store, the three caller bytes, the value byte, the four-byte clear of resweep_wait at the
     partial granule tx + 456) are covered by nd_SH, so none of the report entries 0x8603c,
     0x8646c, 0x8647c, 0x8648c, 0x86498, 0x864a8, 0x864b8 is reached: the caller bytes and tx + 456
     pass the slow block from byte_ok and the block's shadow.
   Image-B boundary rule: no off_img and no `*_imgP` lemma is used here; this segment touches no
   image word, and its atom 32 is the shadow base (not an object index). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts HeadampTxNext.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the scan's index arithmetic, as the symbolic engine builds it -------------------------- *)

Lemma nd_brute144 : forall f g : Z -> Z,
  forallb (fun i => f i =? g i) (map Z.of_nat (seq 0 144)) = true ->
  forall i, 0 <= i < 144 -> f i = g i.
Proof.
  intros f g H i Hi. rewrite forallb_forall in H.
  apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat i). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma nd_divmod : forall i, 0 <= i < 144 ->
  0 <= i / 3 <= 47 /\ 0 <= i mod 3 <= 2 /\ i = 3 * (i / 3) + i mod 3.
Proof.
  intros i Hi. pose proof (Z.div_mod i 3 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound i 3 ltac:(lia)) as Hm.
  set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p. lia.
Qed.

Definition NDMHQ : sv := SMd M_MULHU (SAlu ALU_SLL (SOff 46 0) (SLit 32)) (SLit 12297829383904690176).
Definition NDQ1 : sv := SAlu ALU_SRL NDMHQ (SLit 33).
Definition NDMHP : sv := SMd M_MULHU (SOff 46 0) (SLit 12297829382473034411).
Definition NDQ2 : sv := SAlu ALU_SRL NDMHP (SLit 1).
Definition NDAND : sv := SAlu ALU_AND NDMHP (SLit (-2)).
Definition NDDBL : sv := SAlu ALU_SLL (SOff 51 0) (SLit 1).
Definition NDT3Q : sv := SMd M_MUL (SOff 51 0) (SLit 3).
Definition NDP : sv := SAlu ALU_SUB (SOff 46 0) NDT3Q.
Definition NDNOT : sv := SAlu ALU_XOR (SAlu ALU_ADD (SOff 8 288) NDT3Q) (SLit (-1)).
Definition NDSUM : sv := SAlu ALU_ADD (SOff 8 0) (SOff 46 288).
Definition NDIQ : sv := SAlu ALU_SUB (SOff 46 0) (SOff 51 0).
Definition NDPW : sv := SAlu ALU_SUB (SOff 56 0) NDDBL.
Definition NDA6 : sv := SAlu ALU_ADD (SOff 8 0) NDT3Q.

Lemma nd_UQ1 : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 -> U E NDQ1 = i / 3.
Proof.
  intros E i H Hi. unfold NDQ1, NDMHQ.
  rewrite U_SAlu, U_SMd, U_SAlu, !U_SLit, (U_atom E 46 i H) by lia.
  clear H. revert i Hi. apply nd_brute144. vm_compute. reflexivity.
Qed.

Lemma nd_UQ2 : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 -> U E NDQ2 = i / 3.
Proof.
  intros E i H Hi. unfold NDQ2, NDMHP.
  rewrite U_SAlu, U_SMd, !U_SLit, (U_atom E 46 i H) by lia.
  clear H. revert i Hi. apply nd_brute144. vm_compute. reflexivity.
Qed.

Lemma nd_UAND : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 -> U E NDAND = 2 * (i / 3).
Proof.
  intros E i H Hi. unfold NDAND, NDMHP.
  rewrite U_SAlu, U_SMd, !U_SLit, (U_atom E 46 i H) by lia.
  clear H. revert i Hi. apply nd_brute144. vm_compute. reflexivity.
Qed.

Lemma nd_UDBL : forall E q, ew E 51 = Z_to_bv 64 q -> 0 <= q <= 47 -> U E NDDBL = 2 * q.
Proof.
  intros E q H Hq. unfold NDDBL. rewrite U_SAlu, U_SLit, (U_atom E 51 q H) by lia.
  cbn [zalu_raw]. change (Z.land (zcanon 1) 63) with 1.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma nd_UT3Q : forall E q, ew E 51 = Z_to_bv 64 q -> 0 <= q <= 47 -> U E NDT3Q = 3 * q.
Proof.
  intros E q H Hq. unfold NDT3Q. rewrite U_SMd, U_SLit, (U_atom E 51 q H) by lia.
  cbn [zmd_raw]. change (zcanon 3) with 3.
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma nd_UP : forall E i, ew E 46 = Z_to_bv 64 i -> ew E 51 = Z_to_bv 64 (i / 3) -> 0 <= i < 144 ->
  U E NDP = i mod 3.
Proof.
  intros E i H46 H51 Hi. pose proof (nd_divmod i Hi) as (Q1 & Q2 & Q3).
  set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p.
  unfold NDP. rewrite U_SAlu, (nd_UT3Q E q H51 Q1). rewrite (U_atom E 46 i H46) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma nd_UNOT : forall E tx i, ew E 8 = Z_to_bv 64 tx -> ew E 51 = Z_to_bv 64 (i / 3) ->
  0 <= i < 144 -> 0 <= tx -> tx + 460 <= 2 ^ 47 ->
  U E NDNOT = 18446744073709551615 - (tx + 288 + 3 * (i / 3)).
Proof.
  intros E tx i H8 H51 Hi Ht0 Ht1. pose proof (nd_divmod i Hi) as (Q1 & Q2 & Q3).
  set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p.
  unfold NDNOT. rewrite U_SAlu, U_SAlu, U_SLit, (U_atom_off E 8 tx 288 H8) by lia.
  rewrite (nd_UT3Q E q H51 Q1). cbn [zalu_raw].
  rewrite (zcanon_id (tx + 288 + 3 * q)) by (unfold M64; lia).
  replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity.
  rewrite lxor_allones by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma nd_USUM : forall E tx i, ew E 8 = Z_to_bv 64 tx -> ew E 46 = Z_to_bv 64 i ->
  0 <= i < 144 -> 0 <= tx -> tx + 460 <= 2 ^ 47 -> U E NDSUM = tx + 288 + i.
Proof.
  intros E tx i H8 H46 Hi Ht0 Ht1. unfold NDSUM.
  rewrite U_SAlu, (U_atom E 8 tx H8), (U_atom_off E 46 i 288 H46) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma nd_UIQ : forall E i, ew E 46 = Z_to_bv 64 i -> ew E 51 = Z_to_bv 64 (i / 3) -> 0 <= i < 144 ->
  U E NDIQ = i - i / 3.
Proof.
  intros E i H46 H51 Hi. pose proof (nd_divmod i Hi) as (Q1 & Q2 & Q3).
  set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p.
  unfold NDIQ. rewrite U_SAlu, (U_atom E 46 i H46), (U_atom E 51 q H51) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

Lemma nd_UPW : forall E i, ew E 56 = Z_to_bv 64 (i - i / 3) -> ew E 51 = Z_to_bv 64 (i / 3) ->
  0 <= i < 144 -> U E NDPW = i mod 3.
Proof.
  intros E i H56 H51 Hi. pose proof (nd_divmod i Hi) as (Q1 & Q2 & Q3).
  set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p.
  unfold NDPW. rewrite U_SAlu, (nd_UDBL E q H51 Q1). rewrite (U_atom E 56 (i - q) H56) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma nd_UA6 : forall E tx i, ew E 8 = Z_to_bv 64 tx -> ew E 51 = Z_to_bv 64 (i / 3) ->
  0 <= i < 144 -> 0 <= tx -> tx + 460 <= 2 ^ 47 -> U E NDA6 = tx + 3 * (i / 3).
Proof.
  intros E tx i H8 H51 Hi Ht0 Ht1. pose proof (nd_divmod i Hi) as (Q1 & Q2 & Q3).
  set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p.
  unfold NDA6. rewrite U_SAlu, (nd_UT3Q E q H51 Q1). rewrite (U_atom E 8 tx H8) by lia.
  cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.


(* The scan's end test: the 32-bit count i - 144 + 1 reads 0 exactly at the last cell. *)
Lemma nd_last : forall i, 0 <= i < 144 -> zcanon (i + -143) = zcanon 0 -> i = 143.
Proof.
  intros i Hi H. change (zcanon 0) with 0 in H. unfold zcanon, M64 in H.
  destruct (Z.eq_dec i 143) as [E|Hne]; [exact E|]. exfalso.
  assert (Hm : (i + -143) mod 2 ^ 64 = i + -143 + 2 ^ 64).
  { rewrite <- (Z_mod_plus_full (i + -143) 1). rewrite Z.mul_1_l. apply Z.mod_small. lia. }
  rewrite Hm in H. lia.
Qed.

#[local] Notation TX_SIZE := ATx.TX_SIZE.
#[local] Notation LAY_TX := ATx.LAY_TX.
#[local] Notation tx_vals := ATx.tx_vals.

(* ---- the symbolic state at LOOPD ----------------------------------------------------------- *)

(* The environment's atoms past the 32 registers: 32 the shadow base, 46 the index i, 47 the dirty
   byte's address tx + 288 + i, 48 the value byte's address tx + i, 49 and 50 those two bytes, 51
   the channel i / 3, 53 the complement of tx + 288 (the scan's t3), 54 the parameter i mod 3, 55
   the complement of tx + 288 + 3 (i / 3), 56 i - i / 3, and 60..71 the twelve registers the
   prologue saved (ra, s0..s10), which the epilogue reads back. The machine's own sp (atom 2) is
   the entry sp less image B's 96-byte frame; the table is s0 (atom 8), the value pointer s1
   (atom 9), the channel and parameter pointers a1 and a2 (atoms 11 and 12). *)
Definition nd_extra (regs : bvmap 5 word) (tx i : Z) (T : list byte) : list word :=
  map (Z_to_bv 64)
    [ SB_NX; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
      i; tx + 288 + i; tx + i; tb T (288 + i); tb T i; i / 3; 0;
      18446744073709551615 - (tx + 288); i mod 3;
      18446744073709551615 - (tx + 288 + 3 * (i / 3)); i - i / 3; 0; 0; 0 ]
  ++ [ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
       getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26 ].

Definition ND_PTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition ND_OUT : afact := mkAF 4096 (2 ^ 47 - 1) 0.
Definition ND_N1LO : Z := 18446744073709551615 - 140737479966720 - 288.
Definition ND_N1HI : Z := 18446744073709551615 - 4096 - 288.
Definition ND_N2LO : Z := 18446744073709551615 - 140737479966720 - 288 - 141.

(* The ranges the engine decides the two UBSan guards of the scan (0x85fd0, 0x85ff0) and the
   null guards of the edge (0x8604c, 0x86064, 0x860a4, 0x860ac, 0x860b4) from. *)
Definition nd_atoms : list (nat * afact) :=
  [ (8%nat, ND_PTR 4); (9%nat, ND_OUT); (11%nat, ND_OUT); (12%nat, ND_OUT);
    (32%nat, mkAF SB_NX SB_NX 0);
    (46%nat, mkAF 0 143 0); (47%nat, ND_PTR 0); (48%nat, ND_PTR 0);
    (49%nat, mkAF 0 255 0); (50%nat, mkAF 0 255 0); (51%nat, mkAF 0 47 0);
    (53%nat, mkAF ND_N1LO ND_N1HI 0); (54%nat, mkAF 0 2 0);
    (55%nat, mkAF ND_N2LO ND_N1HI 0); (56%nat, mkAF 0 96 0) ].

(* The two guards no range decides: 0x860a8 (tx + 3c <u tx) and 0x860b0 (tx + i <u tx + 3c). *)
Definition nd_conds : list acond :=
  [ mkAC BC_GEU NDA6 (SOff 8 0); mkAC BC_GEU (SOff 48 0) NDA6 ].

(* The trees the engine builds for c = i / 3 (twice, by two different mulhu reciprocals), 2c,
   p = i mod 3 (twice), the complement of tx + 288 + 3c, and the two byte addresses. *)
Definition nd_alias : list (sv * sv) :=
  [ (NDQ1, SOff 51 0); (NDQ2, SOff 51 0); (NDAND, NDDBL); (NDP, SOff 54 0); (NDNOT, SOff 55 0);
    (SOff 48 288, SOff 47 0); (NDSUM, SOff 47 0); (SOff 47 (-288), SOff 48 0);
    (NDIQ, SOff 56 0); (NDPW, SOff 54 0) ].

Definition sr_d : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (21%bv : bv 5) (SOff 32 0))
    (17%bv : bv 5) (SOff 46 0))
    (14%bv : bv 5) (SOff 46 0))
    (10%bv : bv 5) (SOff 48 0))
    (7%bv : bv 5) (SOff 46 288))
    (6%bv : bv 5) (SOff 46 (-144)))
    (5%bv : bv 5) (SOff 8 288))
    (28%bv : bv 5) (SOff 53 0))
    (29%bv : bv 5) (SLit 12297829382473034411))
    (30%bv : bv 5) (SLit 12297829383904690176).

(* The frame (read-only here; the epilogue reads the twelve saved registers out of it), the
   dirty byte and the value byte. *)
Definition NSTK : YP09.region := YP09.mkRegion (Some 2%nat) 0 96 0 0
  [ YP09.mkChunk 88 (CVal 8 (SOff 60 0)); YP09.mkChunk 80 (CVal 8 (SOff 61 0));
    YP09.mkChunk 72 (CVal 8 (SOff 62 0)); YP09.mkChunk 64 (CVal 8 (SOff 63 0));
    YP09.mkChunk 56 (CVal 8 (SOff 64 0)); YP09.mkChunk 48 (CVal 8 (SOff 65 0));
    YP09.mkChunk 40 (CVal 8 (SOff 66 0)); YP09.mkChunk 32 (CVal 8 (SOff 67 0));
    YP09.mkChunk 24 (CVal 8 (SOff 68 0)); YP09.mkChunk 16 (CVal 8 (SOff 69 0));
    YP09.mkChunk 8 (CVal 8 (SOff 70 0)); YP09.mkChunk 0 (CVal 8 (SOff 71 0)) ].
Definition NDREG : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 49 0))].
Definition NVREG : YP09.region := YP09.mkRegion (Some 48%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 50 0))].
(* What the edge writes: the dirty byte, resweep_wait, and the three bytes the caller holds. *)
Definition NDREGW : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [].
Definition NTXSW : YP09.region := YP09.mkRegion (Some 8%nat) 456 460 456 460 [].
Definition NOUTC : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 1 [].
Definition NOUTP : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 1 [].
Definition NOUTV : YP09.region := YP09.mkRegion (Some 9%nat) 0 1 0 1 [].
Definition nd_regs : list YP09.region := [ NSTK; NDREG; NVREG ].
Definition nd_regs_e : list YP09.region := [ NOUTV; NOUTP; NOUTC; NTXSW; NDREGW; NSTK; NVREG ].
(* The same regions as the edge's run leaves them. *)
Definition NOUTVf : YP09.region := YP09.mkRegion (Some 9%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 50 0))].
Definition NOUTPf : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 54 0))].
Definition NOUTCf : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 51 0))].
Definition NTXSWf : YP09.region := YP09.mkRegion (Some 8%nat) 456 460 456 460 [YP09.mkChunk 456 (CVal 4 (SLit 0))].
Definition NDREGWf : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))].

Definition ss_d : sstate := mkSS LOOPD sr_d nd_regs None (mkFacts nd_atoms nd_conds nd_alias).
Definition nd_SH : list shent :=
  [ mkSHE 8 0 460; mkSHE 11 0 1; mkSHE 12 0 1; mkSHE 9 0 1; mkSHE 47 0 1; mkSHE 48 0 1 ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition ND (regsj regs : bvmap 5 word) (tx i : Z) (T : list byte) : env :=
  Eimg (Ereg regsj (nd_extra regs tx i T)).

Definition nd_env_ok (E : env) (regs : bvmap 5 word) (tx chp parp valp i : Z) (T : list byte) : Prop :=
  ew E 2 = w64 (spZ regs - NX_FRAME) /\ ew E 8 = w64 tx /\ ew E 9 = w64 valp /\
  ew E 11 = w64 chp /\ ew E 12 = w64 parp /\ ew E 32 = w64 SB_NX /\
  ew E 46 = w64 i /\ ew E 47 = w64 (tx + 288 + i) /\ ew E 48 = w64 (tx + i) /\
  ew E 49 = w64 (tb T (288 + i)) /\ ew E 50 = w64 (tb T i) /\ ew E 51 = w64 (i / 3) /\
  ew E 53 = w64 (18446744073709551615 - (tx + 288)) /\ ew E 54 = w64 (i mod 3) /\
  ew E 55 = w64 (18446744073709551615 - (tx + 288 + 3 * (i / 3))) /\ ew E 56 = w64 (i - i / 3) /\
  ew E 60 = getr regs 1 /\ ew E 61 = getr regs 8 /\ ew E 62 = getr regs 9 /\
  ew E 63 = getr regs 18 /\ ew E 64 = getr regs 19 /\ ew E 65 = getr regs 20 /\
  ew E 66 = getr regs 21 /\ ew E 67 = getr regs 22 /\ ew E 68 = getr regs 23 /\
  ew E 69 = getr regs 24 /\ ew E 70 = getr regs 25 /\ ew E 71 = getr regs 26 /\
  ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\ ew E 27 = getr regs 27.

Lemma nd_env_lift : forall E E' regs tx chp parp valp i T,
  (forall n, (n < 72)%nat -> ew E' n = ew E n) ->
  nd_env_ok E regs tx chp parp valp i T -> nd_env_ok E' regs tx chp parp valp i T.
Proof.
  intros E E' regs tx chp parp valp i T HA H. unfold nd_env_ok in *. rewrite !HA by lia. exact H.
Qed.

Lemma nd_env : forall (regsj regs : bvmap 5 word) (tx chp parp valp i : Z) (T : list byte),
  nx_keep_gp regs regsj ->
  getr regsj 2 = w64 (spZ regs - NX_FRAME) ->
  getr regsj 8 = w64 tx -> getr regsj 9 = w64 valp ->
  getr regsj 11 = w64 chp -> getr regsj 12 = w64 parp ->
  nd_env_ok (ND regsj regs tx i T) regs tx chp parp valp i T.
Proof.
  intros regsj regs tx chp parp valp i T HK H2 H8 H9 H11 H12.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew (ND regsj regs tx i T) n = ew (Ereg regsj (nd_extra regs tx i T)) n)
    by (intros n Hn; unfold ND; apply Eimg_low; exact Hn).
  unfold nd_env_ok.
  repeat match goal with |- _ /\ _ => split end;
    rewrite EL by (unfold A_TEXT; lia).
  - rewrite (ew_Ereg_nat regsj _ 2 2%bv eq_refl). exact H2.
  - rewrite (ew_Ereg_nat regsj _ 8 8%bv eq_refl). exact H8.
  - rewrite (ew_Ereg_nat regsj _ 9 9%bv eq_refl). exact H9.
  - rewrite (ew_Ereg_nat regsj _ 11 11%bv eq_refl). exact H11.
  - rewrite (ew_Ereg_nat regsj _ 12 12%bv eq_refl). exact H12.
  - exact (ew_Ereg_extra regsj _ 0).
  - exact (ew_Ereg_extra regsj _ 14).
  - exact (ew_Ereg_extra regsj _ 15).
  - exact (ew_Ereg_extra regsj _ 16).
  - exact (ew_Ereg_extra regsj _ 17).
  - exact (ew_Ereg_extra regsj _ 18).
  - exact (ew_Ereg_extra regsj _ 19).
  - exact (ew_Ereg_extra regsj _ 21).
  - exact (ew_Ereg_extra regsj _ 22).
  - exact (ew_Ereg_extra regsj _ 23).
  - exact (ew_Ereg_extra regsj _ 24).
  - exact (ew_Ereg_extra regsj _ 28).
  - exact (ew_Ereg_extra regsj _ 29).
  - exact (ew_Ereg_extra regsj _ 30).
  - exact (ew_Ereg_extra regsj _ 31).
  - exact (ew_Ereg_extra regsj _ 32).
  - exact (ew_Ereg_extra regsj _ 33).
  - exact (ew_Ereg_extra regsj _ 34).
  - exact (ew_Ereg_extra regsj _ 35).
  - exact (ew_Ereg_extra regsj _ 36).
  - exact (ew_Ereg_extra regsj _ 37).
  - exact (ew_Ereg_extra regsj _ 38).
  - exact (ew_Ereg_extra regsj _ 39).
  - rewrite (ew_Ereg_nat regsj _ 3 3%bv eq_refl). exact (HK 3%bv ltac:(cbn [In]; auto 10)).
  - rewrite (ew_Ereg_nat regsj _ 4 4%bv eq_refl). exact (HK 4%bv ltac:(cbn [In]; auto 10)).
  - rewrite (ew_Ereg_nat regsj _ 27 27%bv eq_refl). exact (HK 27%bv ltac:(cbn [In]; auto 10)).
Qed.

Definition nd_uenv_ok (E : env) (regs : bvmap 5 word) (tx chp parp valp i : Z) (T : list byte) : Prop :=
  bv_unsigned (ew E 2) = spZ regs - NX_FRAME /\ bv_unsigned (ew E 8) = tx /\
  bv_unsigned (ew E 9) = valp /\ bv_unsigned (ew E 11) = chp /\ bv_unsigned (ew E 12) = parp /\
  bv_unsigned (ew E 32) = SB_NX /\ bv_unsigned (ew E 46) = i /\
  bv_unsigned (ew E 47) = tx + 288 + i /\ bv_unsigned (ew E 48) = tx + i /\
  bv_unsigned (ew E 49) = tb T (288 + i) /\ bv_unsigned (ew E 50) = tb T i /\
  bv_unsigned (ew E 51) = i / 3 /\ bv_unsigned (ew E 53) = 18446744073709551615 - (tx + 288) /\
  bv_unsigned (ew E 54) = i mod 3 /\
  bv_unsigned (ew E 55) = 18446744073709551615 - (tx + 288 + 3 * (i / 3)) /\
  bv_unsigned (ew E 56) = i - i / 3.

Lemma nd_uenv : forall E regs tx chp parp valp i T,
  nd_env_ok E regs tx chp parp valp i T ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> 4096 <= tx -> tx + 460 <= 2 ^ 47 ->
  0 <= chp < 2 ^ 64 -> 0 <= parp < 2 ^ 64 -> 0 <= valp < 2 ^ 64 -> 0 <= i < 144 ->
  nd_uenv_ok E regs tx chp parp valp i T.
Proof.
  intros E regs tx chp parp valp i T
    (A2 & A8 & A9 & A11 & A12 & A32 & A46 & A47 & A48 & A49 & A50 & A51 & A53 & A54 & A55 & A56 & _)
    Hsp Htx0 Htx1 Hchp Hparp Hvalp Hi.
  pose proof (ATx.tb_range T (288 + i)) as Rd. pose proof (ATx.tb_range T i) as Rv.
  pose proof (nd_divmod i Hi) as (Q1 & Q2 & Q3).
  unfold nd_uenv_ok.
  rewrite A2, A8, A9, A11, A12, A32, A46, A47, A48, A49, A50, A51, A53, A54, A55, A56.
  set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p.
  unfold w64, NX_FRAME, SB_NX.
  repeat match goal with |- _ /\ _ => split end; apply unsigned_lit_small; lia.
Qed.

(* ---- what two memories that this segment's runs leave alike look like ----------------------- *)
Definition nd_meq (W : world SEGS) (m1 m2 : word -> option byte) : Prop :=
  forall x : word, mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x.

Lemma nd_meq_mbyte : forall W m1 m2 a, nd_meq W m1 m2 ->
  mbyte SEGS (mrestrict (w_H W) m2) a = mbyte SEGS (mrestrict (w_H W) m1) a.
Proof. intros W m1 m2 a H. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma nd_meq_obj : forall W m1 m2 tx T, nd_meq W m1 m2 ->
  obj_at SEGS (mrestrict (w_H W) m1) tx LAY_TX (tx_vals T) ->
  obj_at SEGS (mrestrict (w_H W) m2) tx LAY_TX (tx_vals T).
Proof.
  intros W m1 m2 tx T HQ HO. apply (proj2 (ATx.tx_obj_bytes SEGS _ _ _)). intros kk Hkk.
  rewrite (nd_meq_mbyte W m1 m2 (tx + kk) HQ).
  exact (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HO kk Hkk).
Qed.

Lemma nd_meq_val : forall W m1 m2 a n v, nd_meq W m1 m2 ->
  val_mem SEGS (mrestrict (w_H W) m1) a n v -> val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof. intros W m1 m2 a n v HQ HV kk Hk. rewrite (nd_meq_mbyte W m1 m2 _ HQ). exact (HV kk Hk). Qed.

Lemma nd_meq_saved : forall W m1 m2 regs sp, nd_meq W m1 m2 ->
  nx_saved W m1 regs sp -> nx_saved W m2 regs sp.
Proof.
  intros W m1 m2 regs sp HQ (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold nx_saved. repeat match goal with |- _ /\ _ => split end;
    eapply nd_meq_val; first [exact HQ | eassumption].
Qed.

Lemma nd_meq_pres : forall W m1 m2 a, nd_meq W m1 m2 ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HQ (Hh & b & Hb). split; [exact Hh|]. exists b.
  pose proof (HQ (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Hh in Hx.
  rewrite Hx. exact Hb.
Qed.

Lemma nd_meq_same : forall W memc m1 m2 sp tx chp parp valp d, nd_meq W m1 m2 ->
  nx_same W memc m1 sp tx chp parp valp d -> nx_same W memc m2 sp tx chp parp valp d.
Proof. intros W memc m1 m2 sp tx chp parp valp d HQ HS x H1 H2. rewrite (HQ x). exact (HS x H1 H2). Qed.

Lemma nd_meq_outq : forall W memc m1 m2 chp parp valp, nd_meq W m1 m2 ->
  nx_outq W memc m1 chp parp valp -> nx_outq W memc m2 chp parp valp.
Proof.
  intros W memc m1 m2 chp parp valp HQ (Q1 & Q2 & Q3). unfold nx_outq, aview in *.
  rewrite (nd_meq_mbyte W m1 m2 chp HQ), (nd_meq_mbyte W m1 m2 parp HQ),
    (nd_meq_mbyte W m1 m2 valp HQ).
  repeat split; assumption.
Qed.

Lemma nd_grows_pres : forall (W : world SEGS) m1 m2 a,
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  assert (HN : mrestrict (w_H W) m1 (Z_to_bv 64 a) <> None)
    by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  pose proof (HG _ HN) as H2. unfold mrestrict in H2. rewrite Hh in H2.
  destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:Hb2; [exists b2; reflexivity | exfalso; exact (H2 eq_refl)].
Qed.

(* A run whose regions have no writable window changes nothing. *)
Definition nd_ro (rs : smem) : Prop := forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r.

Lemma nd_ro_nowr : forall E rs a, nd_ro rs -> in_wrange E rs a -> False.
Proof. intros E rs a HR (r & Hin & Ha). pose proof (HR r Hin) as H. lia. Qed.

Lemma nd_ro_awr : forall E rs STK sp0 FP bl0 blc ly own,
  nd_ro rs -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof. intros E rs STK sp0 FP bl0 blc ly own HR a Ha. exfalso. exact (nd_ro_nowr E rs a HR Ha). Qed.

Lemma nd_ro_frame : forall E rs W m1 m2, nd_ro rs ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> nd_meq W m1 m2.
Proof. intros E rs W m1 m2 HR HF x. apply HF. intros Hw. exact (nd_ro_nowr E rs _ HR Hw). Qed.

Lemma nd_ro_regs : nd_ro nd_regs.
Proof.
  intros r Hin. unfold nd_regs in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; unfold NSTK, NDREG, NVREG;
    cbn [YP09.r_wlo YP09.r_whi]; lia.
Qed.

(* The bytes the edge may write. *)
Lemma nd_edge_wr : forall (E : env) (a tx chp parp valp d : Z),
  bv_unsigned (ew E 8) = tx -> bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 9) = valp -> bv_unsigned (ew E 47) = d ->
  in_wrange E nd_regs_e a ->
  (tx + 456 <= a < tx + 460) \/ a = chp \/ a = parp \/ a = valp \/ a = d.
Proof.
  intros E a tx chp parp valp d E8 E11 E12 E9 E47 (r & Hin & Ha).
  unfold nd_regs_e in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]];
    unfold NOUTV, NOUTP, NOUTC, NTXSW, NDREGW, NSTK, NVREG in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite ?E8, ?E11, ?E12, ?E9, ?E47 in Ha; lia.
Qed.

Lemma nd_edge_keep : forall (E : env) (W : world SEGS) m1 m2 (tx chp parp valp d a : Z),
  bv_unsigned (ew E 8) = tx -> bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 9) = valp -> bv_unsigned (ew E 47) = d ->
  frame_of E nd_regs_e (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  0 <= a < 2 ^ 64 ->
  ~ (tx + 456 <= a < tx + 460) -> a <> chp -> a <> parp -> a <> valp -> a <> d ->
  mbyte SEGS (mrestrict (w_H W) m2) a = mbyte SEGS (mrestrict (w_H W) m1) a.
Proof.
  intros E W m1 m2 tx chp parp valp d a E8 E11 E12 E9 E47 HF Ha H1 H2 H3 H4 H5.
  unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  intros Hw.
  destruct (nd_edge_wr E (bv_unsigned (Z_to_bv 64 a)) tx chp parp valp d
              E8 E11 E12 E9 E47 Hw) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    rewrite unsigned_lit_small in Hx by lia; lia.
Qed.

Lemma nd_edge_same : forall (E : env) W memc m1 m2 (sp tx chp parp valp d : Z),
  bv_unsigned (ew E 8) = tx -> bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 9) = valp -> bv_unsigned (ew E 47) = d ->
  frame_of E nd_regs_e (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_same W memc m1 sp tx chp parp valp d ->
  nx_same W memc m2 sp tx chp parp valp d.
Proof.
  intros E W memc m1 m2 sp tx chp parp valp d E8 E11 E12 E9 E47 HF HS x H1 H2.
  rewrite (HF x); [exact (HS x H1 H2)|].
  intros Hw.
  destruct (nd_edge_wr E (bv_unsigned x) tx chp parp valp d E8 E11 E12 E9 E47 Hw)
    as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    apply H2; unfold nx_touch2; lia.
Qed.

Lemma nd_same_dd : forall W memc m sp tx chp parp valp d,
  nx_same W memc m sp tx chp parp valp (tx + 432) ->
  nx_same W memc m sp tx chp parp valp d.
Proof.
  intros W memc m sp tx chp parp valp d HS x H1 H2. apply HS; [exact H1|].
  intros Hc. apply H2. unfold nx_touch2 in *. lia.
Qed.

(* ---- reading a byte back off the symbolic state -------------------------------------------- *)
Lemma nd_chunk_byte : forall E m base off (n : N) (e : sv) (j : Z),
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n e)) -> 0 <= j < Z.of_N n ->
  mbyte SEGS m (base + off + j) = Some (byte_of_word (sv_denot E e) j).
Proof.
  intros E m base off n e j HC Hj. destruct (HC j Hj) as (b & Hb1 & Hb2).
  cbn [YP09.cbyte] in Hb1. injection Hb1 as <-. exact Hb2.
Qed.

Lemma nd_region_chunk : forall E m r c, region_ok SEGS E m r -> In c (YP09.r_chunks r) ->
  YP09.chunk_ok SEGS E m (base_val E (YP09.r_base r)) c.
Proof. intros E m r c (_ & _ & _ & HF) Hin. exact (proj1 (Forall_forall _ _) HF c Hin). Qed.

Lemma nd_st_region : forall E ss ms r, st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) ->
  region_ok SEGS E (ms_mem ms) r.
Proof.
  intros E ss ms r HS Hin.
  destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (_ & HF & _).
  cbn [abs_ss setpc ss_mem] in HF. exact (proj1 (Forall_forall _ _) HF r Hin).
Qed.

Lemma nd_byte_aview : forall (W : world SEGS) m a (z : Z), 0 <= z < 256 ->
  mbyte SEGS (mrestrict (w_H W) m) a = Some (byte_of_word (Z_to_bv 64 z) 0) ->
  aview SEGS (w_H W) m a = Some z.
Proof.
  intros W m a z Hz H. unfold aview. rewrite H. cbn [option_map]. f_equal.
  unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_small z) by (change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma nd_region_w : forall (E : env) (m : word -> option byte) (nn : nat) (base lo hi : Z),
  bv_unsigned (ew E nn) = base -> 0 <= base + lo -> base + hi <= 2 ^ 64 ->
  (forall o, lo <= o < hi -> writable_at SEGS m (base + o)) ->
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi lo hi []).
Proof.
  intros E m nn base lo hi Hb H1 H2 Hw. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hb. split; [exact H1|]. split; [exact H2|]. split; [exact Hw | constructor].
Qed.

Lemma nd_getrZ : forall (regs : bvmap 5 word) (r : bv 5) (z : Z), z = bv_unsigned r ->
  getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
  intros regs r z ->. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma nd_u64 : forall (x : word), 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as H.
  change (bv_modulus 64) with 18446744073709551616 in H.
  change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616. exact H.
Qed.

Lemma nd_lit0 : forall E, sv_denot E (SLit 0) = Z_to_bv 64 0.
Proof. intros E. reflexivity. Qed.

Lemma nd_byte0 : forall (j : Z), 0 <= j -> byte_of_word (Z_to_bv 64 0) j = Z_to_bv 8 0.
Proof.
  intros j Hj. unfold byte_of_word. rewrite (unsigned_lit_small 0) by lia.
  rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma nd_mem_byte : forall (W : world SEGS) E ss (ms : machine_state) (r : YP09.region)
    (nn : nat) (off : Z) (w : N) (e : sv) (a j : Z),
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> In r (ss_mem ss) ->
  YP09.r_base r = Some nn -> In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
  bv_unsigned (ew E nn) = a -> 0 <= j < Z.of_N w ->
  mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (a + off + j) = Some (byte_of_word (sv_denot E e) j).
Proof.
  intros W E ss ms r nn off w e a j HS Hin Hb Hch Ha Hj.
  pose proof (nd_region_chunk E (ms_mem (restrict (w_H W) ms)) r _
                (nd_st_region E ss _ r HS Hin) Hch) as CH.
  rewrite Hb in CH. cbn [base_val] in CH. rewrite Ha in CH.
  cbn [restrict ms_mem] in CH.
  exact (nd_chunk_byte E _ a off w e j CH Hj).
Qed.

Lemma nd_submem : forall E ss ms rs,
  st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms rs HS Hsub Hwf.
  exact (st_ok_submem SEGS E (abs_ss VAL ss) ms rs HS Hsub Hwf).
Qed.

(* ---- the shadow of the three bytes the caller holds is untouched by the walk ---------------- *)
Lemma nd_shadow_apart : forall (tx chp parp valp p : Z),
  in_app tx 460 -> 0 <= p / 8 < 17592186044416 ->
  ~ (SHADOW_OFF <= chp < SHADOW_OFF + 2 ^ 44) ->
  ~ (SHADOW_OFF <= parp < SHADOW_OFF + 2 ^ 44) ->
  ~ (SHADOW_OFF <= valp < SHADOW_OFF + 2 ^ 44) ->
  ~ nx_touch tx chp parp valp (SHADOW_OFF + p / 8).
Proof.
  intros tx chp parp valp p Happ Hdiv Hc Hp Hv.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold nx_touch, ATx.TX_SIZE. intros [Hq | [Hq | [Hq | Hq]]]; lia.
Qed.

Lemma nd_shadow_lo : forall (p : Z), 0 <= p / 8 < 17592186044416 ->
  0 <= SHADOW_OFF + p / 8 < 2 ^ 64.
Proof. intros p Hp. unfold SHADOW_OFF. lia. Qed.

Lemma nd_shadow_stk : forall (p sp : Z), 0 <= p / 8 < 17592186044416 ->
  2 ^ 46 <= sp <= 2 ^ 47 -> ~ (sp - NX_STK <= SHADOW_OFF + p / 8 < sp).
Proof. intros p sp Hp Hsp. rewrite nx_stk_val. unfold SHADOW_OFF. lia. Qed.

Local Ltac nd_dis1 :=
  cbn [all_disjoint ss_mem];
  repeat match goal with |- _ /\ _ => split end; try exact I;
  unfold extent_disjoint;
  cbn [NOUTV NOUTP NOUTC NTXSW NDREGW NSTK NVREG YP09.r_base YP09.r_lo YP09.r_hi base_val];
  unfold NX_FRAME in *; lia.

(* The edge is about to write: the dirty byte, the four bytes of resweep_wait and the three bytes
   the caller holds become writable windows of the symbolic state. *)
Lemma nd_swap : forall (E : env) ss (ms : machine_state) (sp tx chp parp valp d vv : Z),
  st_ok_pi SEGS VAL E ss ms -> ss_mem ss = nd_regs ->
  bv_unsigned (ew E 2) = sp - NX_FRAME -> bv_unsigned (ew E 8) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 9) = valp -> bv_unsigned (ew E 47) = d -> bv_unsigned (ew E 48) = vv ->
  4096 <= tx -> tx + 460 <= sp - NX_FRAME ->
  tx <= d < tx + 432 -> tx <= vv < tx + 432 -> d <> vv ->
  ~ (tx <= chp < tx + 460) -> (chp + 1 <= sp - NX_FRAME \/ sp <= chp) ->
  ~ (tx <= parp < tx + 460) -> (parp + 1 <= sp - NX_FRAME \/ sp <= parp) ->
  ~ (tx <= valp < tx + 460) -> (valp + 1 <= sp - NX_FRAME \/ sp <= valp) ->
  chp <> parp -> chp <> valp -> parp <> valp ->
  region_ok SEGS E (ms_mem ms) NDREGW -> region_ok SEGS E (ms_mem ms) NTXSW ->
  region_ok SEGS E (ms_mem ms) NOUTC -> region_ok SEGS E (ms_mem ms) NOUTP ->
  region_ok SEGS E (ms_mem ms) NOUTV ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) nd_regs_e (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms sp tx chp parp valp d vv HS Hmem E2 E8 E11 E12 E9 E47 E48
    Htx Hstk Hd Hvv Hdv Oc2 Oc3 Op2 Op3 Ov2 Ov3 Dcp Dcv Dpv RD RT RC RP RV.
  assert (HS1 : st_ok_pi SEGS VAL E
            (mkSS (ss_pc ss) (ss_regs ss) [NSTK; NVREG] (ss_resv ss) (ss_facts ss)) ms)
    by (apply (nd_submem E ss ms);
        [exact HS | rewrite Hmem; unfold nd_regs; submem_tac | vm_compute; reflexivity]).
  pose proof (st_ok_pi_add_region E _ ms NDREGW HS1 ltac:(vm_compute; reflexivity) RD
                ltac:(nd_dis1)) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  pose proof (st_ok_pi_add_region E _ ms NTXSW HS2 ltac:(vm_compute; reflexivity) RT
                ltac:(nd_dis1)) as HS3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
  pose proof (st_ok_pi_add_region E _ ms NOUTC HS3 ltac:(vm_compute; reflexivity) RC
                ltac:(nd_dis1)) as HS4.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
  pose proof (st_ok_pi_add_region E _ ms NOUTP HS4 ltac:(vm_compute; reflexivity) RP
                ltac:(nd_dis1)) as HS5.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS5.
  pose proof (st_ok_pi_add_region E _ ms NOUTV HS5 ltac:(vm_compute; reflexivity) RV
                ltac:(nd_dis1)) as HS6.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS6.
  exact HS6.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* A shadow entry for a stretch of a live block that starts inside it. *)
Lemma nd_shent_at : forall ly S (W : world SEGS) mem md Ex (n : nat) (q b sz lo hi : Z),
  AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
  U Ex BxN = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS BxN Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
  intros ly S W mem md Ex n q b sz lo hi HAR Hin HB Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

Lemma nd_edge_awr : forall (E : env) STK sp0 FP ly S lyc Sc own (tx chp parp valp d : Z),
  bv_unsigned (ew E 8) = tx -> bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 9) = valp -> bv_unsigned (ew E 47) = d ->
  tx <= d < tx + TX_SIZE ->
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write B STK sp0 FP ly S lyc Sc own a) ->
  nx_may_write B STK sp0 FP ly S lyc Sc own chp ->
  nx_may_write B STK sp0 FP ly S lyc Sc own parp ->
  nx_may_write B STK sp0 FP ly S lyc Sc own valp ->
  awr_ok E nd_regs_e STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E STK sp0 FP ly S lyc Sc own tx chp parp valp d
    E8 E11 E12 E9 E47 Hd Htab Hc Hp Hv a Ha.
  destruct (nd_edge_wr E a tx chp parp valp d E8 E11 E12 E9 E47 Ha)
    as [Hx | [-> | [-> | [-> | ->]]]].
  - apply Htab. unfold ATx.TX_SIZE in *. lia.
  - exact Hc.
  - exact Hp.
  - exact Hv.
  - apply Htab. exact Hd.
Qed.

(* The symbolic state at the head of the edge scan. *)
Lemma nd_seat : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T : list byte) (i : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals T) ->
  0 <= i < 144 ->
  nx_at_loopd regs regsj tx chp parp valp i ->
  st_ok_pi SEGS VAL (ND regsj regs tx i T) ss_d
    (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + LOOPD)) memj (seg_rom SEGS)))
  /\ sh_ok SEGS BxN nd_SH (ND regsj regs tx i T) (mrestrict (w_H W) memj).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T i HCTX HMID HSAV HOBJ Hi HAT.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav & R456 &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK & HQ).
  pose proof HAT as (HK & R2 & R8 & R9 & R11 & R12 & R21 & R17 & R14 & R10 & R7 & R6 & R5 & R28 & R29 & R30).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (proj1 HJ) as HARj.
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgia & Hgpres & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia, Hgpres.
  pose proof Hgia as Hgapp.
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  assert (WSK : STK_reac_headamp_tx_next = 4208) by reflexivity.
  rewrite nx_stk_val in Hceil. rewrite WSK in Hc3, Hp3, Hv3.
  unfold ATx.TX_SIZE in Hc2, Hp2, Hv2.
  pose proof (ATx.tb_range T (288 + i)) as Rd.
  pose proof (ATx.tb_range T i) as Rv.
  pose proof (nd_divmod i Hi) as (Qd1 & Qd2 & Qd3).
  pose proof (nd_env regsj regs tx chp parp valp i T HK R2 R8 R9 R11 R12) as HE.
  pose proof HE as (E2 & E8 & E9 & E11 & E12 & E32 & E46 & E47 & E48 & E49 & E50 & E51 & E53 & E54 & E55 & E56 &
    E60 & E61 & E62 & E63 & E64 & E65 & E66 & E67 & E68 & E69 & E70 & E71 & E3 & E4 & E27).
  pose proof (nd_uenv (ND regsj regs tx i T) regs tx chp parp valp i T HE
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU.
  pose proof HU as (U2 & U8 & U9 & U11 & U12 & U32 & U46 & U47 & U48 & U49 & U50 & U51 & U53 & U54 & U55 & U56).
  clear HCTX HMID HE HU HI HJ HAR Hobjc Hpresc Hret Hra4 Hgp Htp
    Q10 Q11 Q12 Q13 Hwtab Hwc Hwp Hwv Pc Pp Pv Hgia Hgpres HpresS HpresK HTL HQ R456.
  set (E := ND regsj regs tx i T) in *.
  assert (HUB : U E BxN = SHADOW_OFF)
    by (unfold U, BxN; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact U32).
  split.
  - rewrite restrict_mkst_fx. unfold ss_d. apply pa_entry_st_ok_full.
    + unfold sr_d.
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R30].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R29].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite E53, Z.add_0_r, Z_to_bv_bv_unsigned; exact R28].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite U8, R5; reflexivity].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite U46, R6; unfold w64; f_equal; lia].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite U46, R7; unfold w64; f_equal; lia].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite E48, Z.add_0_r, Z_to_bv_bv_unsigned; exact R10].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; exact R14].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; exact R17].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact R21].
      unfold E, ND. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold nd_regs, NSTK, NDREG, NVREG.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U2. unfold NX_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        pose proof HSAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 88 8 (SOff 60 0) (bv_unsigned (getr regs 1)));
             [ cbn [sv_denot]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 88) with (spZ regs - 8) by lia; exact S1 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 80 8 (SOff 61 0) (bv_unsigned (getr regs 8)));
             [ cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 80) with (spZ regs - 16) by lia; exact S2 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 72 8 (SOff 62 0) (bv_unsigned (getr regs 9)));
             [ cbn [sv_denot]; rewrite E62, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 72) with (spZ regs - 24) by lia; exact S3 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 64 8 (SOff 63 0) (bv_unsigned (getr regs 18)));
             [ cbn [sv_denot]; rewrite E63, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 64) with (spZ regs - 32) by lia; exact S4 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 56 8 (SOff 64 0) (bv_unsigned (getr regs 19)));
             [ cbn [sv_denot]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 56) with (spZ regs - 40) by lia; exact S5 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 48 8 (SOff 65 0) (bv_unsigned (getr regs 20)));
             [ cbn [sv_denot]; rewrite E65, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 48) with (spZ regs - 48) by lia; exact S6 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 40 8 (SOff 66 0) (bv_unsigned (getr regs 21)));
             [ cbn [sv_denot]; rewrite E66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 40) with (spZ regs - 56) by lia; exact S7 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 32 8 (SOff 67 0) (bv_unsigned (getr regs 22)));
             [ cbn [sv_denot]; rewrite E67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 32) with (spZ regs - 64) by lia; exact S8 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 24 8 (SOff 68 0) (bv_unsigned (getr regs 23)));
             [ cbn [sv_denot]; rewrite E68, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 24) with (spZ regs - 72) by lia; exact S9 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 16 8 (SOff 69 0) (bv_unsigned (getr regs 24)));
             [ cbn [sv_denot]; rewrite E69, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 16) with (spZ regs - 80) by lia; exact S10 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 8 8 (SOff 70 0) (bv_unsigned (getr regs 25)));
             [ cbn [sv_denot]; rewrite E70, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 8) with (spZ regs - 88) by lia; exact S11 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs - 96) 0 8 (SOff 71 0) (bv_unsigned (getr regs 26)));
             [ cbn [sv_denot]; rewrite E71, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs - 96 + 0) with (spZ regs - 96) by lia; exact S12 ].
      * rewrite U47. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [| apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (tx + 288 + i) 0 1 (SOff 49 0) (tb T (288 + i)));
          [ cbn [sv_denot]; rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |].
        replace (tx + 288 + i + 0) with (tx + (288 + i)) by lia.
        exact (ATx.tx_cell_val SEGS _ tx T (288 + i) ltac:(lia) HOBJ).
      * rewrite U48. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [| apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (tx + i) 0 1 (SOff 50 0) (tb T i));
          [ cbn [sv_denot]; rewrite E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |].
        replace (tx + i + 0) with (tx + i) by lia.
        exact (ATx.tx_cell_val SEGS _ tx T i ltac:(lia) HOBJ).
    + apply pairwise_disjoint_of_extents.
      unfold nd_regs, NSTK, NDREG, NVREG, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U2, U47, U48.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hspr Hceil Hgceil Hg4096 Hi C1. clear. unfold NX_FRAME. intros.
      repeat split; lia.
    + split; [| split].
      * cbn [nd_atoms f_atoms atoms_ok]. unfold afact_ok, ND_PTR, ND_OUT, ND_N1LO, ND_N1HI, ND_N2LO.
        cbn [af_lo af_hi af_al2].
        rewrite U8, U9, U11, U12, U32, U46, U47, U48, U49, U50, U51, U53, U54, U55, U56.
        change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
        revert Hg16 Hg4096 Hgceil Hi Rd Rv Hc0 Hc1 Hp0 Hp1 Hv0 Hv1 C1 Qd1 Qd2 Qd3.
        clear. unfold SB_NX. intros.
        set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p.
        repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [nd_conds f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
        rewrite !branch_geu_U.
        rewrite (nd_UA6 E tx i E8 E51 Hi ltac:(lia) ltac:(lia)).
        rewrite (U_atom E 8 tx E8), (U_atom E 48 (tx + i) E48) by lia.
        set (q := i / 3) in *. set (p := i mod 3) in *. clearbody q p.
        split; [| split; [| exact I]]; apply negb_true_iff, Z.ltb_ge; lia.
      * cbn [nd_alias f_alias alias_ok].
        repeat match goal with |- _ /\ _ => split end; try exact I; apply U_inj.
        -- rewrite (nd_UQ1 E i E46 Hi), (U_atom E 51 (i / 3) E51) by lia. reflexivity.
        -- rewrite (nd_UQ2 E i E46 Hi), (U_atom E 51 (i / 3) E51) by lia. reflexivity.
        -- rewrite (nd_UAND E i E46 Hi), (nd_UDBL E (i / 3) E51 Qd1). reflexivity.
        -- rewrite (nd_UP E i E46 E51 Hi), (U_atom E 54 (i mod 3) E54) by lia. reflexivity.
        -- rewrite (nd_UNOT E tx i E8 E51 Hi ltac:(lia) ltac:(lia)).
           rewrite (U_atom E 55 _ E55) by (set (q := i / 3) in *; clearbody q; lia). reflexivity.
        -- rewrite (U_atom_off E 48 (tx + i) 288 E48), (U_atom E 47 (tx + 288 + i) E47) by lia. lia.
        -- rewrite (nd_USUM E tx i E8 E46 Hi ltac:(lia) ltac:(lia)), (U_atom E 47 (tx + 288 + i) E47) by lia.
           reflexivity.
        -- rewrite (U_atom_off E 47 (tx + 288 + i) (-288) E47), (U_atom E 48 (tx + i) E48) by lia. lia.
        -- rewrite (nd_UIQ E i E46 E51 Hi), (U_atom E 56 (i - i / 3) E56) by lia. reflexivity.
        -- rewrite (nd_UPW E i E56 E51 Hi), (U_atom E 54 (i mod 3) E54) by lia. reflexivity.
  - assert (RAj : forall p, 4096 <= p -> p + 1 <= 2 ^ 47 ->
      ~ (SHADOW_OFF <= p < SHADOW_OFF + 2 ^ 44) ->
      range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 1 ->
      range_addressable (aview SEGS (w_H W) memj) SHADOW_OFF p 1).
    { intros pz Hz0 Hz1 Hz5 Hra.
      apply (range_addressable_agree (aview SEGS (w_H W) memc)); [| exact Hra].
      intros x Hx. assert (x = pz) as -> by lia.
      assert (Hdiv : 0 <= pz / 8 < 17592186044416)
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      unfold shadow_of_addr.
      apply (nx_same_aview W memc memj (spZ regs) tx chp parp valp (tx + 432) (SHADOW_OFF + pz / 8));
        [ exact HSAME
        | exact (nd_shadow_lo pz Hdiv)
        | unfold ATx.TX_SIZE; lia
        | exact (nd_shadow_stk pz (spZ regs) Hdiv Hspr)
        | exact (nd_shadow_apart tx chp parp valp pz Hgapp Hdiv Hc5 Hp5 Hv5) ]. }
    unfold sh_ok, nd_SH.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    + apply (shent_ok_of_block SEGS B LAWS lyc Sc W memj mdj E BxN 8 tx TX_SIZE 0 460 HARj Hg HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U8.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 11 chp 1 chp 0 1
               (RAj chp ltac:(lia) ltac:(lia) ltac:(exact Hc5) Rac) HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U11.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with chp by lia. exact Hc5.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 12 parp 1 parp 0 1
               (RAj parp ltac:(lia) ltac:(lia) ltac:(exact Hp5) Rap) HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U12.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with parp by lia. exact Hp5.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 9 valp 1 valp 0 1
               (RAj valp ltac:(lia) ltac:(lia) ltac:(exact Hv5) Rav) HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with valp by lia. exact Hv5.
    + apply (nd_shent_at lyc Sc W memj mdj E 47 (tx + 288 + i) tx TX_SIZE 0 1 HARj Hg HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U47.
      * lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (nd_shent_at lyc Sc W memj mdj E 48 (tx + i) tx TX_SIZE 0 1 HARj Hg HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U48.
      * lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
Qed.

Local Ltac ndenv Hold Hnew :=
  lazymatch type of Hold with
  | nd_env_ok _ ?rg ?tx ?chp ?parp ?valp ?i ?T =>
    lazymatch goal with
    | HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
      assert (Hnew : nd_env_ok Ex rg tx chp parp valp i T)
        by (eapply nd_env_lift;
            [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact Hold])
    end
  end.

Local Ltac nd_clr :=
  repeat match goal with
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end.

(* The edge scan: by induction on the cells left. *)
Lemma nx_dloop : nx_after_stmt B -> nx_dloop_stmt B.
Proof.
intros KAFTR. unfold nx_dloop_stmt.
intros n. induction n as [|n IH]; intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
  tx chp parp valp T i HCTX HMID HSAV HOBJ HACT Hi Hn Hz HAT; [lia|].
pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav & R456 &
  Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
  Q10 & Q11 & Q12 & Q13 & HTL & HI & Hobjc & Hpresc).
pose proof HMID as (HJ & HSAME & HpresS & HpresK & HQ).
pose proof HAT as (HK & R2 & R8 & R9 & R11 & R12 & R21 & R17 & R14 & R10 & R7 & R6 & R5 & R28 & R29 & R30).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARj.
destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
  as (Hg16 & Hg4096 & Hgceil & Hgia & Hgpres & _).
change (req_size TX_SIZE) with 460 in Hgceil, Hgia, Hgpres.
assert (Bc : 4096 <= chp < 2 ^ 47) by (destruct Hoc as (? & ? & _); lia).
assert (Bp : 4096 <= parp < 2 ^ 47) by (destruct Hop as (? & ? & _); lia).
assert (Bv : 4096 <= valp < 2 ^ 47) by (destruct Hov as (? & ? & _); lia).
assert (Hceil' : alloc_ceiling <= spZ regs - 4208) by (rewrite <- nx_stk_val; exact Hceil).
assert (WSK : STK_reac_headamp_tx_next = 4208) by reflexivity.
clear Hgia.
pose proof (ATx.tb_range T (288 + i)) as Rd.
pose proof (ATx.tb_range T i) as Rvb.
pose proof (nd_divmod i Hi) as (Qd1 & Qd2 & Qd3).
destruct (nd_seat STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
  tx chp parp valp T i HCTX HMID HSAV HOBJ Hi HAT) as [HS SHOK].
pose proof (nd_env regsj regs tx chp parp valp i T HK R2 R8 R9 R11 R12) as HE0.
remember (ND regsj regs tx i T) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (rewrite HEdef; unfold ND; apply Eimg_env).
clear HEdef.
unfold cfg_at. change (w64 (BASE + LOOPD)) with (Z_to_bv 64 (BASE + LOOPD)).
(* the shadow check and load of the dirty byte, with the two UBSan guards 0x85fd0 / 0x85ff0
   decided from the facts of atoms 53 / 51 and 55 / 54 *)
paj_run_tok RUN HS HJ SHOK BspanN; [apply nd_ro_awr; exact nd_ro_regs |].
lazymatch goal with
| HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (nd_ro_frame _ _ W m1 m2 nd_ro_regs HFr) as MQ1
end.
nd_clr.
pose proof HE0 as (A2 & A8 & A9 & A11 & A12 & A32 & A46 & A47 & A48 & A49 & A50 & A51 & A53 & A54 & A55 & A56 &
  A60 & A61 & A62 & A63 & A64 & A65 & A66 & A67 & A68 & A69 & A70 & A71 & A3 & A4 & A27).
pose proof (nd_uenv _ regs tx chp parp valp i T HE0
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU0.
pose proof HU0 as (AU2 & AU8 & AU9 & AU11 & AU12 & AU32 & AU46 & AU47 & AU48 & AU49 & AU50 &
  AU51 & AU53 & AU54 & AU55 & AU56).
ndenv HE0 HE1. clear HE0 HU0.
pose proof HE1 as (F2 & F8 & F9 & F11 & F12 & F32 & F46 & F47 & F48 & F49 & F50 & F51 & F53 & F54 & F55 & F56 &
  F60 & F61 & F62 & F63 & F64 & F65 & F66 & F67 & F68 & F69 & F70 & F71 & F3 & F4 & F27).
pose proof (nd_uenv _ regs tx chp parp valp i T HE1
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU1.
pose proof HU1 as (G2 & G8 & G9 & G11 & G12 & G32 & G46 & G47 & G48 & G49 & G50 &
  G51 & G53 & G54 & G55 & G56).
psrr_branch_tok RUN BR HS SHOK BspanN.
- (* the cell is dirty: the edge emits the record *)
  rewrite branch_ne_U, (U_atom _ 49 _ F49), U_lit in Hc by lia.
  rewrite negb_true_iff in Hc. apply Z.eqb_neq in Hc.
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (PRtx : forall a, tx <= a < tx + 460 -> apresent (w_H W) (ms_mem msx) a)
      by (intros a Ha; eapply nd_meq_pres; [exact MQ1|]; apply Hgpres; lia);
    assert (PRc : apresent (w_H W) (ms_mem msx) chp)
      by (eapply nd_meq_pres; [exact MQ1|]; apply HpresK; exact Pc);
    assert (PRp : apresent (w_H W) (ms_mem msx) parp)
      by (eapply nd_meq_pres; [exact MQ1|]; apply HpresK; exact Pp);
    assert (PRv : apresent (w_H W) (ms_mem msx) valp)
      by (eapply nd_meq_pres; [exact MQ1|]; apply HpresK; exact Pv)
  end.
  assert (Oc2 : ~ (tx <= chp < tx + 460))
    by (destruct Hoc as (_ & _ & X & _); unfold ATx.TX_SIZE in X; exact X).
  assert (Oc3 : chp + 1 <= spZ regs - NX_FRAME \/ spZ regs <= chp)
    by (destruct Hoc as (_ & _ & _ & X & _); rewrite WSK in X; unfold NX_FRAME; lia).
  assert (Op2 : ~ (tx <= parp < tx + 460))
    by (destruct Hop as (_ & _ & X & _); unfold ATx.TX_SIZE in X; exact X).
  assert (Op3 : parp + 1 <= spZ regs - NX_FRAME \/ spZ regs <= parp)
    by (destruct Hop as (_ & _ & _ & X & _); rewrite WSK in X; unfold NX_FRAME; lia).
  assert (Ov2 : ~ (tx <= valp < tx + 460))
    by (destruct Hov as (_ & _ & X & _); unfold ATx.TX_SIZE in X; exact X).
  assert (Ov3 : valp + 1 <= spZ regs - NX_FRAME \/ spZ regs <= valp)
    by (destruct Hov as (_ & _ & _ & X & _); rewrite WSK in X; unfold NX_FRAME; lia).
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
    assert (RD : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) NDREGW)
      by (unfold NDREGW; apply (nd_region_w _ _ 47 (tx + 288 + i) 0 1 G47 ltac:(lia) ltac:(lia));
          intros o Ho; replace (tx + 288 + i + o) with (tx + (288 + i)) by lia;
          apply (apresent_writable SEGS); apply PRtx; lia);
    assert (RT : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) NTXSW)
      by (unfold NTXSW; apply (nd_region_w _ _ 8 tx 456 460 G8 ltac:(lia) ltac:(lia));
          intros o Ho; apply (apresent_writable SEGS); apply PRtx; lia);
    assert (RC : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) NOUTC)
      by (unfold NOUTC; apply (nd_region_w _ _ 11 chp 0 1 G11 ltac:(lia) ltac:(lia));
          intros o Ho; replace (chp + o) with chp by lia;
          apply (apresent_writable SEGS); exact PRc);
    assert (RP : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) NOUTP)
      by (unfold NOUTP; apply (nd_region_w _ _ 12 parp 0 1 G12 ltac:(lia) ltac:(lia));
          intros o Ho; replace (parp + o) with parp by lia;
          apply (apresent_writable SEGS); exact PRp);
    assert (RV : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) NOUTV)
      by (unfold NOUTV; apply (nd_region_w _ _ 9 valp 0 1 G9 ltac:(lia) ltac:(lia));
          intros o Ho; replace (valp + o) with valp by lia;
          apply (apresent_writable SEGS); exact PRv)
  end.
  pose proof (nd_swap _ _ _ (spZ regs) tx chp parp valp (tx + 288 + i) (tx + i)
    HS eq_refl G2 G8 G11 G12 G9 G47 G48 ltac:(lia) ltac:(unfold NX_FRAME; lia) ltac:(lia) ltac:(lia)
    ltac:(lia) Oc2 Oc3 Op2 Op3 Ov2 Ov3 Dcp Dcv Dpv RD RT RC RP RV) as HS1.
  clear HS. rename HS1 into HS.
  (* the store check and clear of the dirty byte, the stores of channel, parameter and value
     (UBSan guards 0x8604c / 0x86064 / 0x860a4 / 0x860ac / 0x860b4 from the atoms' facts,
     0x860a8 / 0x860b0 from nd_conds), the four-byte clear of resweep_wait, and the epilogue *)
  paj_run_tok RUN HS HJ SHOK BspanN;
    [ apply (nd_edge_awr _ STK sp0 FP ly S lyc Sc own tx chp parp valp (tx + 288 + i));
      [ exact G8 | exact G11 | exact G12 | exact G9 | exact G47
      | unfold ATx.TX_SIZE; lia | exact Hwtab | exact Hwc | exact Hwp | exact Hwv ] |].
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ => pose proof HFr as FR2
  end.
  lazymatch goal with
  | HGx : mem_grows _ _ |- _ => pose proof HGx as GR2
  end.
  ndenv HE1 HE2.
  pose proof HE2 as (K2 & K8 & K9 & K11 & K12 & K32 & K46 & K47 & K48 & K49 & K50 & K51 & K53 & K54 & K55 & K56 &
    K60 & K61 & K62 & K63 & K64 & K65 & K66 & K67 & K68 & K69 & K70 & K71 & K3 & K4 & K27).
  pose proof (nd_uenv _ regs tx chp parp valp i T HE2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU2.
  pose proof HU2 as (N2 & N8 & N9 & N11 & N12 & N32 & N46 & N47 & N48 & N49 & N50 &
    N51 & N53 & N54 & N55 & N56).
  (* the bytes the edge wrote, read back off the symbolic state *)
  pose proof (nd_mem_byte W _ _ _ NOUTVf 9 0 1 (SOff 50 0) valp 0 HS
    ltac:(cbn [ss_mem]; left; reflexivity) eq_refl ltac:(cbn [YP09.r_chunks]; left; reflexivity)
    N9 ltac:(cbn; lia)) as BYv.
  pose proof (nd_mem_byte W _ _ _ NOUTPf 12 0 1 (SOff 54 0) parp 0 HS
    ltac:(cbn [ss_mem]; right; left; reflexivity) eq_refl ltac:(cbn [YP09.r_chunks]; left; reflexivity)
    N12 ltac:(cbn; lia)) as BYp.
  pose proof (nd_mem_byte W _ _ _ NOUTCf 11 0 1 (SOff 51 0) chp 0 HS
    ltac:(cbn [ss_mem]; right; right; left; reflexivity) eq_refl
    ltac:(cbn [YP09.r_chunks]; left; reflexivity) N11 ltac:(cbn; lia)) as BYc.
  pose proof (nd_mem_byte W _ _ _ NDREGWf 47 0 1 (SLit 0) (tx + 288 + i) 0 HS
    ltac:(cbn [ss_mem]; right; right; right; right; left; reflexivity) eq_refl
    ltac:(cbn [YP09.r_chunks]; left; reflexivity) N47 ltac:(cbn; lia)) as BYd.
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (BYw : forall j, 0 <= j < 4 ->
      mbyte SEGS (mrestrict (w_H W) (ms_mem msx)) (tx + 456 + j) = Some (Z_to_bv 8 0))
      by (intros j Hj;
          rewrite (nd_mem_byte W _ _ _ NTXSWf 8 456 4 (SLit 0) tx j HS
            ltac:(cbn [ss_mem]; right; right; right; left; reflexivity) eq_refl
            ltac:(cbn [YP09.r_chunks]; left; reflexivity) N8 ltac:(cbn; lia));
          rewrite nd_lit0, nd_byte0 by lia; reflexivity)
  end.
  (* the registers at the ret *)
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbn [ms_regs ms_mem].
  rewrite P1, A60. unfold YK0s.ret_ok in Hret. rewrite Hret.
  eapply (nx_finish B LAWS) with (d := tx + 288 + i)
    (T' := set4 (setb T (288 + i) 0) 456 0) (r := 1) (c := i / 3) (p := i mod 3) (v := tb T i).
  + unfold ATx.TX_SIZE. lia.
  + exact HAR.
  + exact Hg.
  + exact Hoc.
  + exact Hop.
  + exact Hov.
  + exact Hspr.
  + exact Hceil.
  + rewrite (nx_model_edge T tx i HACT ltac:(lia) Hz Hc). reflexivity.
  + apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
  + (* the registers the call keeps *)
    intros r Hr.
    assert (Hcs : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
                  r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by (clear - Hr; unfold acallee_saved in Hr; lia).
    clear Hr.
    destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    * rewrite !(nd_getrZ _ (2%bv : bv 5) 2 eq_refl), P2, AU2. unfold NX_FRAME.
      replace (spZ regs - 96 + 96) with (spZ regs) by lia.
      unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * rewrite !(nd_getrZ _ (3%bv : bv 5) 3 eq_refl), P3. exact A3.
    * rewrite !(nd_getrZ _ (4%bv : bv 5) 4 eq_refl), P4. exact A4.
    * rewrite !(nd_getrZ _ (8%bv : bv 5) 8 eq_refl), P8. exact A61.
    * rewrite !(nd_getrZ _ (9%bv : bv 5) 9 eq_refl), P9. exact A62.
    * rewrite !(nd_getrZ _ (18%bv : bv 5) 18 eq_refl), P18. exact A63.
    * rewrite !(nd_getrZ _ (19%bv : bv 5) 19 eq_refl), P19. exact A64.
    * rewrite !(nd_getrZ _ (20%bv : bv 5) 20 eq_refl), P20. exact A65.
    * rewrite !(nd_getrZ _ (21%bv : bv 5) 21 eq_refl), P21. exact A66.
    * rewrite !(nd_getrZ _ (22%bv : bv 5) 22 eq_refl), P22. exact A67.
    * rewrite !(nd_getrZ _ (23%bv : bv 5) 23 eq_refl), P23. exact A68.
    * rewrite !(nd_getrZ _ (24%bv : bv 5) 24 eq_refl), P24. exact A69.
    * rewrite !(nd_getrZ _ (25%bv : bv 5) 25 eq_refl), P25. exact A70.
    * rewrite !(nd_getrZ _ (26%bv : bv 5) 26 eq_refl), P26. exact A71.
    * rewrite !(nd_getrZ _ (27%bv : bv 5) 27 eq_refl), P27. exact A27.
  + (* what the walk left untouched *)
    eapply (nd_edge_same _ W memc _ _ (spZ regs) tx chp parp valp (tx + 288 + i)
              G8 G11 G12 G9 G47 FR2).
    eapply nd_meq_same; [exact MQ1|].
    apply nd_same_dd. exact HSAME.
  + intros a Ha. eapply nd_grows_pres; [exact GR2|].
    eapply nd_meq_pres; [exact MQ1|]. exact (HpresS a Ha).
  + intros a Ha. eapply nd_grows_pres; [exact GR2|].
    eapply nd_meq_pres; [exact MQ1|]. apply HpresK. exact Ha.
  + rewrite P10. cbn [sv_denot]. reflexivity.
  + (* the table *)
    clear - HTL HOBJ MQ1 FR2 BYd BYw G8 G11 G12 G9 G47 Hi Hg4096 Hgceil C1 Oc2 Op2 Ov2.
    apply (proj2 (ATx.tx_obj_bytes SEGS _ _ _)). intros kk Hkk.
    pose proof (ATx.tx_fbyte_range kk Hkk) as Hkr.
    destruct (Z.eq_dec kk (288 + i)) as [-> | Hne].
    * rewrite <- Z_to_bv8_tb.
      rewrite (tb_set4_out (setb T (288 + i) 0) 456 0 (288 + i)
                 ltac:(apply len_setb; [exact HTL | lia]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite (tb_setb_in T (288 + i) 0 HTL ltac:(lia) ltac:(lia)).
      replace (tx + (288 + i)) with (tx + 288 + i + 0 + 0) by lia.
      rewrite BYd, nd_lit0, nd_byte0 by lia. reflexivity.
    * destruct (Z.le_gt_cases 456 kk) as [Hk456 | Hk456].
      -- rewrite <- Z_to_bv8_tb.
         replace kk with (456 + (kk - 456)) by lia.
         rewrite (tb_set4_in (setb T (288 + i) 0) 456 0 (kk - 456)
                    ltac:(apply len_setb; [exact HTL | lia]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
         assert (Hj4 : kk - 456 = 0 \/ kk - 456 = 1 \/ kk - 456 = 2 \/ kk - 456 = 3) by lia.
         replace (tx + (456 + (kk - 456))) with (tx + 456 + (kk - 456)) by lia.
         rewrite (BYw (kk - 456) ltac:(lia)).
         destruct Hj4 as [-> | [-> | [-> | ->]]]; cbn [nth Z.to_nat]; reflexivity.
      -- rewrite <- Z_to_bv8_tb.
         rewrite (tb_set4_out (setb T (288 + i) 0) 456 0 kk
                    ltac:(apply len_setb; [exact HTL | lia]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
         rewrite (tb_setb_out T (288 + i) 0 kk HTL ltac:(lia) ltac:(lia) ltac:(lia)).
         rewrite Z_to_bv8_tb.
         rewrite (nd_edge_keep _ W _ _ tx chp parp valp (tx + 288 + i) (tx + kk)
                    G8 G11 G12 G9 G47 FR2
                    ltac:(clear - Hkr Hg4096 Hgceil C1; lia) ltac:(clear - Hk456; lia)
                    ltac:(clear - Hkr Oc2; lia) ltac:(clear - Hkr Op2; lia) ltac:(clear - Hkr Ov2; lia)
                    ltac:(clear - Hne; lia)).
         rewrite (nd_meq_mbyte W memj _ (tx + kk) MQ1).
         exact (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HOBJ kk Hkk).
  + (* the invariant the contract asks to keep *)
    pose proof (thd_ok_next T tx HTL HI) as HOK.
    rewrite (nx_model_edge T tx i HACT ltac:(lia) Hz Hc) in HOK.
    unfold nxT, edge_res in HOK. cbn [snd] in HOK. exact HOK.
  + (* the three bytes the caller holds *)
    intros _. split; [| split].
    * apply (nd_byte_aview W _ chp (i / 3)); [lia |].
      replace chp with (chp + 0 + 0) by lia. rewrite BYc.
      cbn [sv_denot]. rewrite K51, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * apply (nd_byte_aview W _ parp (i mod 3)); [lia |].
      replace parp with (parp + 0 + 0) by lia. rewrite BYp.
      cbn [sv_denot]. rewrite K54, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * apply (nd_byte_aview W _ valp (tb T i)); [lia |].
      replace valp with (valp + 0 + 0) by lia. rewrite BYv.
      cbn [sv_denot]. rewrite K50, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + intros H0. discriminate H0.
- (* the cell is clean: the scan steps to the next one *)
  rewrite branch_ne_U, (U_atom _ 49 _ F49), U_lit in Hc by lia.
  rewrite negb_false_iff in Hc. apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK BspanN; [apply nd_ro_awr; exact nd_ro_regs |].
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (nd_ro_frame _ _ W m1 m2 nd_ro_regs HFr) as MQ2
  end.
  nd_clr.
  ndenv HE1 HE2.
  pose proof HE2 as (K2 & K8 & K9 & K11 & K12 & K32 & K46 & K47 & K48 & K49 & K50 & K51 & K53 & K54 & K55 & K56 &
    K60 & K61 & K62 & K63 & K64 & K65 & K66 & K67 & K68 & K69 & K70 & K71 & K3 & K4 & K27).
  psrr_branch_tok RUN BR HS SHOK BspanN;
  [ lazymatch goal with H : branch_taken BC_EQ _ _ = true |- _ => rename H into HcB end
  | lazymatch goal with H : branch_taken BC_EQ _ _ = false |- _ => rename H into HcB end ].
  + (* the scan has run out: the walk goes on at AFTR *)
    rewrite branch_eq_U, U_SOff, K46, U_SLit in HcB. unfold w64 in HcB.
    rewrite unsigned_lit_small in HcB by lia.
    apply Z.eqb_eq in HcB. apply (nd_last i Hi) in HcB.
    paj_run_to_tok RUNTO HS HJ SHOK BspanN AFTR; [apply nd_ro_awr; exact nd_ro_regs |].
    lazymatch goal with
    | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (nd_ro_frame _ _ W m1 m2 nd_ro_regs HFr) as MQ3
    end.
    nd_clr.
    ndenv HE2 HE3.
    pose proof HE3 as (L2 & L8 & L9 & L11 & L12 & L32 & L46 & L47 & L48 & L49 & L50 & L51 & L53 & L54 & L55 & L56 &
      L60 & L61 & L62 & L63 & L64 & L65 & L66 & L67 & L68 & L69 & L70 & L71 & L3 & L4 & L27).
    prreg HS (2%bv : bv 5) P2. prreg HS (21%bv : bv 5) P21.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
    prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
    prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (27%bv : bv 5) P27.
    pmkst HS.
    lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rgA _ ?mmA _) ?mdA) _ =>
      apply (KAFTR STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rgA mmA mdA tx chp parp valp T)
    end.
    * exact HCTX.
    * split; [exact HJ|]. split.
      -- eapply nd_meq_same; [exact MQ3|]. eapply nd_meq_same; [exact MQ2|].
         eapply nd_meq_same; [exact MQ1|]. exact HSAME.
      -- split; [| split].
         ++ intros a Ha. eapply nd_meq_pres; [exact MQ3|]. eapply nd_meq_pres; [exact MQ2|].
            eapply nd_meq_pres; [exact MQ1|]. apply HpresS. exact Ha.
         ++ intros a Ha. eapply nd_meq_pres; [exact MQ3|]. eapply nd_meq_pres; [exact MQ2|].
            eapply nd_meq_pres; [exact MQ1|]. apply HpresK. exact Ha.
         ++ eapply nd_meq_outq; [exact MQ3|]. eapply nd_meq_outq; [exact MQ2|].
            eapply nd_meq_outq; [exact MQ1|]. exact HQ.
    * eapply nd_meq_saved; [exact MQ3|]. eapply nd_meq_saved; [exact MQ2|].
      eapply nd_meq_saved; [exact MQ1|]. exact HSAV.
    * eapply nd_meq_obj; [exact MQ3|]. eapply nd_meq_obj; [exact MQ2|].
      eapply nd_meq_obj; [exact MQ1|]. exact HOBJ.
    * exact HACT.
    * intros l Hl. destruct (Z.eq_dec l i) as [-> | Hne]; [exact Hc | apply Hz; lia].
    * split; [| repeat match goal with |- _ /\ _ => split end].
      -- intros r Hr. cbn [In] in Hr.
         destruct Hr as [<- | [<- | [<- | []]]].
         ++ rewrite P3. exact A3.
         ++ rewrite P4. exact A4.
         ++ rewrite P27. exact A27.
      -- rewrite P2. exact A2.
      -- rewrite P8. exact A8.
      -- rewrite P9. exact A9.
      -- rewrite P11. exact A11.
      -- rewrite P12. exact A12.
      -- rewrite P21. exact A32.
  + (* the scan steps: the next cell *)
    rewrite branch_eq_U, U_SOff, K46, U_SLit in HcB. unfold w64 in HcB.
    rewrite unsigned_lit_small in HcB by lia.
    apply Z.eqb_neq in HcB.
    assert (Hi1 : i <> 143) by (intros ->; apply HcB; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK BspanN LOOPD; [apply nd_ro_awr; exact nd_ro_regs |].
    lazymatch goal with
    | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (nd_ro_frame _ _ W m1 m2 nd_ro_regs HFr) as MQ3
    end.
    nd_clr.
    ndenv HE2 HE3.
    pose proof HE3 as (L2 & L8 & L9 & L11 & L12 & L32 & L46 & L47 & L48 & L49 & L50 & L51 & L53 & L54 & L55 & L56 &
      L60 & L61 & L62 & L63 & L64 & L65 & L66 & L67 & L68 & L69 & L70 & L71 & L3 & L4 & L27).
    prreg HS (2%bv : bv 5) P2. prreg HS (21%bv : bv 5) P21.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
    prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
    prreg HS (17%bv : bv 5) P17. prreg HS (14%bv : bv 5) P14.
    prreg HS (10%bv : bv 5) P10. prreg HS (7%bv : bv 5) P7.
    prreg HS (6%bv : bv 5) P6. prreg HS (5%bv : bv 5) P5.
    prreg HS (28%bv : bv 5) P28. prreg HS (29%bv : bv 5) P29. prreg HS (30%bv : bv 5) P30.
    prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (27%bv : bv 5) P27.
    pmkst HS.
    lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rgA _ ?mmA _) ?mdA) _ =>
      apply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rgA mmA mdA
               tx chp parp valp T (i + 1))
    end.
    * exact HCTX.
    * split; [exact HJ|]. split.
      -- eapply nd_meq_same; [exact MQ3|]. eapply nd_meq_same; [exact MQ2|].
         eapply nd_meq_same; [exact MQ1|]. exact HSAME.
      -- split; [| split].
         ++ intros a Ha. eapply nd_meq_pres; [exact MQ3|]. eapply nd_meq_pres; [exact MQ2|].
            eapply nd_meq_pres; [exact MQ1|]. apply HpresS. exact Ha.
         ++ intros a Ha. eapply nd_meq_pres; [exact MQ3|]. eapply nd_meq_pres; [exact MQ2|].
            eapply nd_meq_pres; [exact MQ1|]. apply HpresK. exact Ha.
         ++ eapply nd_meq_outq; [exact MQ3|]. eapply nd_meq_outq; [exact MQ2|].
            eapply nd_meq_outq; [exact MQ1|]. exact HQ.
    * eapply nd_meq_saved; [exact MQ3|]. eapply nd_meq_saved; [exact MQ2|].
      eapply nd_meq_saved; [exact MQ1|]. exact HSAV.
    * eapply nd_meq_obj; [exact MQ3|]. eapply nd_meq_obj; [exact MQ2|].
      eapply nd_meq_obj; [exact MQ1|]. exact HOBJ.
    * exact HACT.
    * lia.
    * lia.
    * intros l Hl. destruct (Z.eq_dec l i) as [-> | Hne]; [exact Hc | apply Hz; lia].
    * split; [| repeat match goal with |- _ /\ _ => split end].
      -- intros r Hr. cbn [In] in Hr.
         destruct Hr as [<- | [<- | [<- | []]]].
         ++ rewrite P3. exact A3.
         ++ rewrite P4. exact A4.
         ++ rewrite P27. exact A27.
      -- rewrite P2. exact A2.
      -- rewrite P8. exact A8.
      -- rewrite P9. exact A9.
      -- rewrite P11. exact A11.
      -- rewrite P12. exact A12.
      -- rewrite P21. exact A32.
      -- rewrite P17, AU46. unfold w64; f_equal; lia.
      -- rewrite P14, AU46. unfold w64; f_equal; lia.
      -- rewrite P10, AU48. unfold w64; f_equal; lia.
      -- rewrite P7, AU46. unfold w64; f_equal; lia.
      -- rewrite P6, AU46. unfold w64; f_equal; lia.
      -- rewrite P5, AU8. unfold w64; f_equal; lia.
      -- rewrite P28. exact A53.
      -- rewrite P29. cbn [sv_denot]. reflexivity.
      -- rewrite P30. cbn [sv_denot]. reflexivity.
Qed.

End h.
End f.
End d.
