(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 480 of its 523 lines of code are new or changed and 426 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanInner.v at 26536c34173b for
   reac-pw/fuzz_rate's image A: role's pcs (I 0x821e0 .. 0x822a4, KM 0x822a8, ABS 0x82380) become rate's (0x829e4 ..
   0x82aa8, 0x82aac, 0x82b7c), the registers are renamed as rate's code has them (the shadow offset s7 -> s2, the
   type constant s10 -> s9, n_ent - 1 s4 -> s3, m s5 -> s6, m + 1 s9 -> s7), the cut file is lib/A/RtPgSeg.v
   (rl_ -> rt_, e_pp -> q_pp), the first block's facts come from lib/A/RtPgMem.v (rm_ -> rtm_), the image facts
   from lib/A/RtPgSteps.v, and the cut-list lemmas and the checks' base from lib/A/RtPgScanKit.v. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgScanInner.v at fa28558fbb17 for image B
   (fuzz_rate.asan-ubsan); image B's inner loop is rotated (cut I 0x82b74 after the head 0x82b70, exits to I, KM
   0x82c40 and ABS 0x82d1c), its bases are fixed with s8 = 104 m as the offset, its key test is branch-free
   (`snez; addi; and`), and three trap tests are stepped over by closed-numeral atom ranges; the cut file is
   lib/AU/RtPgSegB.v, the block facts lib/AU/RtPgMemB.v, the post and the list lemmas lib/AU/RtPgScanKitB.v. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the piece "one turn of the
   inner scan" of the walk of LLVMFuzzerTestOneInput, lib/AU/RtPgSegB.v rsb_piece_W11a_inner_stmt. Proves no
   function (kind: segment lemma).

   THE CODE (I 0x82b74 .. 0x82c0c and the loop head 0x82b70, pod_next_pair's inner loop with pod_string inlined,
   pod.h:90-96 and :134-142). At I, s2 = &ent[0], a7 = &ent[0] + 4, t2 = s7 = &ent[0] + 8, s8 = 104 m, s6 = a2 = m,
   a3 = 33, s11 = ~&ent[0], a4 = ~(&ent[0] + 8) - 104 m, t3 = 8, s10 = n_ent, s4 = the runtime's shadow offset.
     0x82b74             beq a3,s6 -> 0x83098: a trap test, not taken (a3 = 33, s6 = m <= 31)
     0x82b78             bltu s11,s8 -> 0x83098: a trap test, not taken (&ent[m] does not wrap)
     0x82b7c .. 0x82b8c  a0 := s2 + s8 = &ent[m]; the instrumented check of its 4 bytes (slow block 0x82c14)
     0x82b90 .. 0x82b94  lw a1,0(a0) (type); bne a1,t3: not a String, to 0x82bf8
     0x82b98 .. 0x82ba8  a1 := a7 + s8 = &ent[m].size; its check (slow block 0x82c24)
     0x82bac .. 0x82bb0  lw a0,4(a0) (size); beqz a0: size 0, to 0x82bfc with a0 = 0
     0x82bb4 .. 0x82bbc  a0 := D = zext32 (size - 1)
     0x82bc0             bltu a4,a0 -> 0x83098: a trap test, not taken (&body[size - 1] does not wrap)
     0x82bc4 .. 0x82bd8  a5 := s8 + D + t2 = P = &ent[m].body[size - 1]; its 1-byte check (slow block 0x82c34)
     0x82bdc .. 0x82bf4  lbu of the byte at s7 + s8 + D = P; a0 := (snez byte - 1) & (s7 + s8): the body address
                         when the byte is NUL, else 0 (no branch on the byte); j 0x82bfc
     0x82bf8             li a0,0: not a String
     0x82bfc .. 0x82c08  s6 := m + 1; s8 := 104 (m + 1); a2 := m + 1 (addiw); a4 := a4 - 104
     0x82c0c             bltu s6,s10: back to the head 0x82b70, else 0x82c10 j ABS 0x82d1c
     0x82b70             bnez a0 -> KM 0x82c40: a key; else I 0x82b74 with m + 1
   The slow blocks' error jumps (0x82c20, 0x82c30, 0x82c3c) are never reached, nor is 0x83098. No store and no call:
   the turn writes no byte and changes no float register.

   HOW. si_blk is the turn as a block lemma over the machine state at I (lib/Reusable: the token engine YCbn.v, the
   journal YCbq.v), stated for any float state. Its entry state has the registers as atoms and six more atoms: A =
   &ent[m] (32), the type t (33), the size z (34), D = (z - 1) mod 2^32 (35), P = A + 8 + max (z - 1, 0) (36) and
   the byte lb at P (37). Alias facts make every address the code computes an atom plus a constant: s2 + s8 is A,
   a7 + s8 is A + 4, s7 + s8 is A + 8, the zero extension of size - 1 is D, and (added once size <> 0 is known, when
   D = z - 1) t2 + s8 + D and s7 + s8 + D are P. Two read-only regions hold the two words at A and the byte at P. The
   shadow base is s4 itself (atom 20, SHADOW_OFF), and the two shadow entries [A - 4, A + 108) and [P, P + 8) cover
   the 8 bytes from each check's address, so the engine reads each shadow byte as 0 and decides each `bnez` not taken
   (the entries are paid from the first block's shadow, RtPgMemB.rtmb_blk_ra). The atom ranges are closed numerals:
   a3 in [33, 33] and s6 in [0, 31] decide the `beq`, s11 in [2^64 - 2^47 + 4095, 2^64 - 0x4015] above s8 in
   [0, 3224] decides the first `bltu`, a4 in [2^64 - 2^47 + 863, 2^64 - 0x401d] above D in [0, 2^32 - 1] the second;
   a2's range [0, 31] lets the engine keep the `addiw` as a2 + 1. The engine splits the four branches it cannot
   decide (the type, the size, m + 1 < n_ent and the head's `bnez` on the branch-free key value) and runs each arm
   to its end pc. The post is RtPgScanKitB.skb_post (the journal, the memory and the 23 registers of si_kept_regs
   as at I). rkb_inner_B reads I's cut, reads the three fields out of the first block's image
   (RtPgMemB.rtmb_pp_ent), runs si_blk at the run's own float state, and rebuilds the cut of the arm: ABS (entry m
   is the last one: the answer is (None, 0) by RtPgScanFB.rkb_inv_last), I at m + 1 (the entry is not a key) or KM
   (the entry is a key: the three tests are Accessors.key_of's three conjuncts). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB RtPgScanFB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgScanKitB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ================================ the code table and the entry state ================================ *)
(* the 52 words 0x82b70 .. 0x82c3c (the loop head, the turn and the three slow blocks); the end pc I 0x82b74 is its
   second word, KM 0x82c40 and ABS 0x82d1c lie outside it *)
Definition si_tbl : ctable := build_table rsegs 0x82b70 52 TEmpty.
Lemma si_tbl_ok : table_ok rsegs si_tbl.
Proof. apply build_table_ok0. lia. Qed.

(* the shadow base: register s4 (atom 20) holds SHADOW_OFF *)
Definition SISB : Z := 0x7fff8000.
Definition SIBx : sv := SOff 20 0.
Definition SIBspan : Z * Z := (SISB, SISB + 2 ^ 44 - 1).

(* the two read-only regions: the type and size words at A (atom 32), the byte at P (atom 36) *)
Definition si_R1 : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))].
Definition si_R2 : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
(* the zero extension of size - 1, in the form the engine builds for 0x82bb4 .. 0x82bbc *)
Definition si_zx : sv :=
  SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 32)) (SLit (-4294967296))) (SLit 32).
(* s2 + s8 = A (0x82b7c), a7 + s8 = A + 4 (0x82b98), s7 + s8 = A + 8 (0x82be4), zext32 (size - 1) = D *)
Definition si_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 18 0) (SOff 24 0), SOff 32 0);
    (SAlu ALU_ADD (SOff 17 0) (SOff 24 0), SOff 32 4);
    (SAlu ALU_ADD (SOff 23 0) (SOff 24 0), SOff 32 8);
    (si_zx, SOff 35 0) ].
(* added once size <> 0 is known: t2 + s8 + D (0x82bc8) and s7 + s8 + D (0x82bdc) are P *)
Definition si_aP7 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 7 0) (SOff 24 0)) (SOff 35 0).
Definition si_aP23 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 23 0) (SOff 24 0)) (SOff 35 0).
(* the atom ranges, closed numerals: s4 = SHADOW_OFF; a3 = 33; a2 = s6 = m <= 31; s8 = 104 m <= 3224;
   s11 = ~&ent[0] and a4 = ~(&ent[0] + 8) - 104 m as 64-bit words, for &ent[0] in [0x4014, 2^47 - 0x1000];
   A, t, z, D, P and the byte *)
Definition si_facts : facts :=
  mkFacts [ (20%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 33 33 0);
            (12%nat, mkAF 0 31 0); (22%nat, mkAF 0 31 0); (24%nat, mkAF 0 3224 0);
            (27%nat, mkAF 18446603336221200383 18446744073709535211 0);
            (14%nat, mkAF 18446603336221197151 18446744073709535203 0);
            (32%nat, mkAF 16404 140737488354816 0); (33%nat, mkAF 0 4294967295 0); (34%nat, mkAF 0 45 0);
            (35%nat, mkAF 0 4294967295 0); (36%nat, mkAF 16412 140737488355072 0); (37%nat, mkAF 0 255 0) ]
          [] si_alias.
Definition si_ss0 : sstate := mkSS RSB_I sr_atoms [si_R1; si_R2] None si_facts.
Definition si_SH : list shent := [mkSHE 32 (-4) 108; mkSHE 36 0 8].
(* the six atoms after the registers *)
Definition si_D (z : Z) : Z := (z - 1) mod 2 ^ 32.
Definition si_P (A z : Z) : Z := A + 8 + Z.of_nat (Z.to_nat (z - 1)).
Definition si_extra (A t z lb : Z) : list word :=
  [w64 A; w64 t; w64 z; w64 (si_D z); w64 (si_P A z); w64 lb].
(* the three tests of pod_string *)
Definition si_key (t z lb : Z) : bool := (t =? 8) && (1 <=? z) && (lb =? 0).
(* the registers the turn does not write (all but a0, a1, a2, a4, a5, a6, s6, s8); the cuts' lists name only these
   and the four the arms set *)
Definition si_kept_regs : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 17; 18; 19; 20; 21; 23; 25; 26; 27; 28; 29; 30; 31].

(* ================================ arithmetic ================================ *)
Lemma si_zx_U : forall E z, ew E 34 = Z_to_bv 64 z -> 0 <= z <= 45 -> U E si_zx = si_D z.
Proof.
intros E z H Hz. unfold si_zx, si_D.
rewrite !U_SAlu, !U_SLit, (U_atom E 34 z H) by lia. cbn [zalu_raw].
rewrite (zcanon_id 32) by (unfold M64; lia). change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon, M64. change (-4294967296 mod 2 ^ 64) with (2 ^ 64 - 2 ^ 32).
rewrite (Z.mod_small (z * 2 ^ 32)) by lia.
destruct (Z.eq_dec z 0) as [->|Hz0]; [reflexivity|].
replace (z * 2 ^ 32 + (2 ^ 64 - 2 ^ 32)) with ((z - 1) * 2 ^ 32 + 1 * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. rewrite (Z.mod_small ((z - 1) * 2 ^ 32)) by lia. rewrite Z.div_mul by lia.
rewrite (Z.mod_small (z - 1) (2 ^ 32)) by lia. apply Z.mod_small. lia.
Qed.

Lemma si_sext_U : forall E t, ew E 33 = Z_to_bv 64 t -> 0 <= t < 2 ^ 32 ->
(U E (SExt true 32 (SOff 33 0)) =? 8) = (t =? 8).
Proof.
intros E t H Ht. rewrite U_SExt, (U_atom E 33 t H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small t) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
unfold zcanon, M64.
destruct (Z.ltb_spec t (2 ^ 31)) as [Hl|Hg].
- rewrite (Z.mod_small (t + 2 ^ 31)) by lia. replace (t + 2 ^ 31 - 2 ^ 31) with t by lia.
  rewrite Z.mod_small by lia. reflexivity.
- replace (t + 2 ^ 31) with ((t + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by ring.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (t + 2 ^ 31 - 2 ^ 32)) by lia.
  replace (t + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((t + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (t + 2 ^ 64 - 2 ^ 32) 8); [lia|]. destruct (Z.eqb_spec t 8); [lia | reflexivity].
Qed.

(* the branch-free key value of 0x82be8 .. 0x82bf0: (snez lb - 1) & (A + 8) *)
Lemma si_and_U : forall E A lb, ew E 32 = Z_to_bv 64 A -> 0 <= A -> A + 8 < 2 ^ 64 ->
ew E 37 = Z_to_bv 64 lb -> 0 <= lb < 256 ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 37 0)) (SLit (-1))) (SOff 32 8)) =
if lb =? 0 then A + 8 else 0.
Proof.
intros E A lb H32 HA0 HA1 H37 Hlb.
rewrite !U_SAlu, !U_SLit, (U_atom E 37 lb H37), (U_atom_off E 32 A 8 H32) by lia. cbn [zalu_raw].
change (zcanon 0) with 0. change (zcanon (-1)) with (2 ^ 64 - 1).
destruct (Z.eq_dec lb 0) as [->|Hne].
- change (0 <? 0) with false. cbv iota. change (zcanon 0) with 0. rewrite Z.add_0_l.
  rewrite (zcanon_id (2 ^ 64 - 1)) by (unfold M64; lia).
  rewrite Z.land_comm. change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia. cbn [Z.eqb]. apply zcanon_id. unfold M64. lia.
- replace (0 <? lb) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota. change (zcanon 1) with 1.
  replace (1 + (2 ^ 64 - 1)) with (2 ^ 64) by ring. change (zcanon (2 ^ 64)) with 0. rewrite Z.land_0_l.
  replace (lb =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
Qed.

(* two names of one 64-bit word *)
Lemma si_w64_add : forall u v, v = u + 2 ^ 64 -> w64 u = w64 v.
Proof.
intros u v H. subst v. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite <- (Z_mod_plus_full u 1 (2 ^ 64)). f_equal; lia.
Qed.

(* ================================ the entry's bytes ================================ *)
Lemma si_firstn4 : forall (a b : list byte), length a = 4%nat -> firstn 4 (a ++ b) = a.
Proof. intros a b H. rewrite firstn_app, H, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia. Qed.
Lemma si_slice_type : forall e, rtmb_slice (ent_mem e) 0 4 = Z_to_le_bytes 4 (e_type e).
Proof. intros e. unfold rtmb_slice, ent_mem. cbn [skipn]. apply si_firstn4. apply length_le32. Qed.
Lemma si_slice_size : forall e, rtmb_slice (ent_mem e) 4 4 = Z_to_le_bytes 4 (e_size e).
Proof.
intros e. unfold rtmb_slice, ent_mem. rewrite skipn_app, length_le32, Nat.sub_diag, skipn_O.
rewrite skipn_all2 by (rewrite length_le32; lia). cbn [app]. apply si_firstn4. apply length_le32.
Qed.
Lemma si_nth_zeros : forall (l : list byte) n k, nth k (l ++ zeros n) NUL = nth k l NUL.
Proof.
intros l n k. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
- apply app_nth1. exact Hk.
- rewrite app_nth2 by exact Hk. rewrite (nth_overflow l) by exact Hk. unfold zeros. apply nth_repeat.
Qed.
Lemma si_nth_body : forall e k, nth (8 + k) (ent_mem e) (Z_to_bv 8 0) = nth k (e_body e) NUL.
Proof.
intros e k. change (Z_to_bv 8 0) with NUL. unfold ent_mem.
rewrite app_nth2 by (rewrite length_le32; lia). rewrite length_le32.
rewrite app_nth2 by (rewrite length_le32; lia). rewrite length_le32.
replace (8 + k - 4 - 4)%nat with k by lia. apply si_nth_zeros.
Qed.

(* membership in the kept registers, and the post's register facts *)
Ltac si_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
Ltac si_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RtPgStepsB.same_io_wvb]; kio] in kio.
(* the memory after a run over the read-only regions is the memory at I *)
Ltac si_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac si_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok si_tbl_ok HS HJ SHOK SIBspan; [awr_ok_tac | ] end.
Ltac si_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok si_tbl_ok HS HJ SHOK SIBspan pc; [awr_ok_tac | ] end.
Ltac si_branch Hc := lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok si_tbl_ok HS SHOK SIBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac si_in := unfold rsb_L_scan, rsb_L_chk, rsb_Hc; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac si_kin := unfold si_kept_regs; apply in_map; cbn [In]; lia.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* what the back edge to I computes (a4 is the bound's 64-bit word at entry) *)
Definition si_I_R (j x a4 : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 12) = w64 (j + 1) /\ getr regs2 (Z_to_bv 5 22) = w64 (j + 1) /\
getr regs2 (Z_to_bv 5 24) = w64 (x + 104) /\ getr regs2 (Z_to_bv 5 14) = w64 (a4 - 104).
(* what the exit to KM computes *)
Definition si_KM_R (A j x : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 10) = w64 (A + 8) /\ getr regs2 (Z_to_bv 5 12) = w64 (j + 1) /\
getr regs2 (Z_to_bv 5 22) = w64 (j + 1) /\ getr regs2 (Z_to_bv 5 24) = w64 (x + 104).

(* the leaves of the run tree (used inside si_blk only: they name its hypotheses) *)
(* a register the arm advanced: SOff n c over the atom n, whose value En gives *)
Ltac si_adv :=
si_sv;
lazymatch goal with |- sv_denot _ (SOff ?n ?c) = w64 ?v =>
  lazymatch goal with En : ew _ n = Z_to_bv 64 ?v0 |- _ =>
    rewrite (skb_soff _ n v0 c En); unfold w64; f_equal; lia end end.
Ltac si_kept :=
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HAE : env_agree 32 (Ereg ?rg ?ex0) _ |- _ =>
  intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict _ ms) rg ex0 si_kept_regs HS HAE
    ltac:(vm_compute; reflexivity) r Hr) end.
Ltac si_post_intro :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), HM : ms_mem ?ms = _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rewrite HM in HJ;
  eapply (skb_post_intro B); [exact HS | reflexivity | reflexivity | exact HM | exact HJ | si_io | si_kept | ] end.
(* the exit at 0x82c10: m + 1 >= n_ent *)
Ltac si_abs Hl :=
si_run_to RSB_ABS; si_mem; apply SRr_ret; left;
split; [apply Z.ltb_ge in Hl; exact Hl|];
si_post_intro; exact I.
(* the back edge through the head 0x82b70 to I *)
Ltac si_Ileaf Hk Hl :=
si_run_to RSB_I; si_mem; apply SRr_ret; right; left;
split; [apply Z.ltb_lt in Hl; exact Hl|];
split; [exact Hk|];
si_post_intro;
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  unfold si_I_R; rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end;
repeat split; si_adv.
(* the `bltu s6,s10` at 0x82c0c *)
Ltac si_last Hl :=
si_branch Hl;
lazymatch goal with E22 : ew ?E 22 = Z_to_bv 64 ?j, E26 : ew ?E 26 = Z_to_bv 64 ?n |- _ =>
  rewrite branch_ltu_U, (U_atom_off E 22 j 1 E22), (U_atom E 26 n E26) in Hl by lia end.
(* an entry that is not a key: on to the `bltu`, then I or ABS *)
Ltac si_nk Hk := si_run; si_mem; let Hl := fresh "Hl" in si_last Hl; [si_Ileaf Hk Hl | si_abs Hl].

Lemma si_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(b0 x A t z lb j n : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 18) = w64 b0 -> getr regs (Z_to_bv 5 17) = w64 (b0 + 4) ->
getr regs (Z_to_bv 5 7) = w64 (b0 + 8) -> getr regs (Z_to_bv 5 23) = w64 (b0 + 8) ->
getr regs (Z_to_bv 5 24) = w64 x ->
getr regs (Z_to_bv 5 27) = w64 (2 ^ 64 - 1 - b0) ->
getr regs (Z_to_bv 5 14) = w64 (2 ^ 64 - 9 - b0 - x) ->
getr regs (Z_to_bv 5 13) = w64 33 ->
getr regs (Z_to_bv 5 12) = w64 j -> getr regs (Z_to_bv 5 22) = w64 j ->
getr regs (Z_to_bv 5 26) = w64 n -> getr regs (Z_to_bv 5 28) = w64 8 ->
getr regs (Z_to_bv 5 20) = w64 SHADOW_OFF ->
A = b0 + x -> x = 104 * j ->
0x4014 <= b0 <= 2 ^ 47 - 0x1000 -> 0 <= t < 2 ^ 32 -> 0 <= z <= 45 -> 0 <= lb < 256 ->
0 <= j <= 31 -> 0 <= n <= 32 ->
val_mem rsegs (mrestrict (w_H W) memc) A 4 t ->
val_mem rsegs (mrestrict (w_H W) memc) (A + 4) 4 z ->
val_mem rsegs (mrestrict (w_H W) memc) (si_P A z) 1 lb ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (A - 4) 112 ->
(forall a, A - 4 <= a < A + 108 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs RSB_I regs memc mdc)
(fun W2 c2 =>
 (n <= j + 1 /\
  skb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RSB_ABS si_kept_regs (fun _ => True) W2 c2) \/
 (j + 1 < n /\ si_key t z lb = false /\
  skb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RSB_I si_kept_regs
    (si_I_R j x (2 ^ 64 - 9 - b0 - x)) W2 c2) \/
 (j + 1 < n /\ si_key t z lb = true /\
  skb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RSB_KM si_kept_regs (si_KM_R A j x) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b0 x A t z lb j n HJ
  H18 H17 H7 H23 H24 H27 H14 H13 H12 H22 H26 H28 H20 HAx Hxj Hb0 Ht Hz Hlb Hj Hn Vt Vz Vb HRA Happ.
pose proof RtPgStepsB.rtsb_wx as Hwx. pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (si_extra A t z lb) as ex eqn:Hex.
assert (EA : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (Ereg regs ex) n0 = getr regs r)
  by (intros n0 r Hr; exact (ew_Ereg_nat regs _ n0 r Hr)).
assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 b0) by (rewrite (EA 18%nat (Z_to_bv 5 18) eq_refl); exact H18).
assert (E17 : ew (Ereg regs ex) 17 = Z_to_bv 64 (b0 + 4)) by (rewrite (EA 17%nat (Z_to_bv 5 17) eq_refl); exact H17).
assert (E7 : ew (Ereg regs ex) 7 = Z_to_bv 64 (b0 + 8)) by (rewrite (EA 7%nat (Z_to_bv 5 7) eq_refl); exact H7).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 (b0 + 8)) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 x) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 (2 ^ 64 - 1 - b0))
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E14 : ew (Ereg regs ex) 14 = Z_to_bv 64 (2 ^ 64 - 9 - b0 - x))
  by (rewrite (EA 14%nat (Z_to_bv 5 14) eq_refl); exact H14).
assert (E13 : ew (Ereg regs ex) 13 = Z_to_bv 64 33) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E12 : ew (Ereg regs ex) 12 = Z_to_bv 64 j) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E22 : ew (Ereg regs ex) 22 = Z_to_bv 64 j) by (rewrite (EA 22%nat (Z_to_bv 5 22) eq_refl); exact H22).
assert (E26 : ew (Ereg regs ex) 26 = Z_to_bv 64 n) by (rewrite (EA 26%nat (Z_to_bv 5 26) eq_refl); exact H26).
assert (E28 : ew (Ereg regs ex) 28 = Z_to_bv 64 8) by (rewrite (EA 28%nat (Z_to_bv 5 28) eq_refl); exact H28).
assert (E20 : ew (Ereg regs ex) 20 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 A) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 t) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 z) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 (si_D z)) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew (Ereg regs ex) 36 = Z_to_bv 64 (si_P A z)) by (subst ex; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew (Ereg regs ex) 37 = Z_to_bv 64 lb) by (subst ex; exact (ew_Ereg_extra regs _ 5)).
assert (HD : 0 <= si_D z < 2 ^ 32) by (unfold si_D; apply Z.mod_pos_bound; lia).
assert (HP : A + 8 <= si_P A z <= A + 52) by (unfold si_P; lia).
assert (HS : st_ok rsegs (Ereg regs ex) si_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 RSB_I) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold si_ss0. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold si_R1, si_R2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ A 0 4 (SOff 33 0) t); [rewrite skb_denot0; exact E33 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vt.
      * apply (chunk_ok_val rsegs _ _ A 4 4 (SOff 34 0) z); [rewrite skb_denot0; exact E34 | cbn; lia | cbn; lia |].
        exact Vz.
    + rewrite E36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (si_P A z) 0 1 (SOff 37 0) lb); [rewrite skb_denot0; exact E37 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, si_R1, si_R2. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E32, E36, !unsigned_lit_small by lia. left. lia.
  - split; [|split; [exact I|]].
    + cbn [si_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E20, E13, E12, E22, E24, E27, E14, E32, E33, E34, E35, E36, E37, !unsigned_lit_small
        by (unfold SHADOW_OFF; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
    + cbn [si_facts f_alias alias_ok si_alias]. unfold si_zx.
      repeat split; apply U_inj.
      * rewrite U_SAlu, (U_atom _ 18 b0 E18), (U_atom _ 24 x E24), (U_atom _ 32 A E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 17 (b0 + 4) E17), (U_atom _ 24 x E24), (U_atom_off _ 32 A 4 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 23 (b0 + 8) E23), (U_atom _ 24 x E24), (U_atom_off _ 32 A 8 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * fold si_zx. rewrite (si_zx_U _ z E34 Hz), (U_atom _ 35 (si_D z) E35) by lia. reflexivity. }
assert (U20 : U (Ereg regs ex) SIBx = SHADOW_OFF) by (apply U_atom; [exact E20 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs SIBx si_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, si_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H W) memc _ SIBx 32 (A - 4) 112 A (-4) 108 HRA U20); [| lia | lia |].
    + apply U_atom; [exact E32 | lia].
    + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia.
  - apply (shent_ok_of_range rsegs (w_H W) memc _ SIBx 36 (A - 4) 112 (si_P A z) 0 8 HRA U20); [| lia | lia |].
    + apply U_atom; [exact E36 | lia].
    + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 RSB_I) with (Z_to_bv 64 RSB_I).
(* 0x82b74 .. 0x82b90: the two trap tests, &ent[m]'s check and the type's load; stop at 0x82b94 bne a1,t3 *)
si_run. si_mem.
si_branch Hty;
  rewrite branch_ne_U, (U_atom E 28 8 E28), (si_sext_U E t E33 Ht) in Hty by lia.
- (* taken: not a String; 0x82bf8 a0 := 0 *)
  apply negb_true_iff in Hty.
  assert (Hk : si_key t z lb = false) by (unfold si_key; rewrite Hty; reflexivity).
  si_nk Hk.
- (* the type is 8: 0x82b98 .. 0x82bac, the size's check and load; stop at 0x82bb0 beqz a0 *)
  apply negb_false_iff in Hty.
  si_run. si_mem.
  si_branch Hsz;
    rewrite branch_eq_U, (U_atom E 34 z E34), (U_lit E 0) in Hsz by lia.
  + (* size 0: not a key; 0x82bfc with a0 = 0 *)
    assert (Hk : si_key t z lb = false).
    { unfold si_key. replace (1 <=? z) with false by (symmetry; apply Z.leb_gt; apply Z.eqb_eq in Hsz; lia).
      rewrite andb_false_r. reflexivity. }
    si_nk Hk.
  + (* size >= 1: t2 + s8 + D and s7 + s8 + D are P; 0x82bb4 .. 0x82c08, the trap test, the last byte's check
       and load, the branch-free key value and the advance; stop at 0x82c0c bltu s6,s10 *)
    apply Z.eqb_neq in Hsz.
    assert (HaP7 : sv_denot E si_aP7 = sv_denot E (SOff 36 0)).
    { apply U_inj. unfold si_aP7.
      rewrite !U_SAlu, (U_atom E 7 (b0 + 8) E7), (U_atom E 24 x E24), (U_atom E 35 (si_D z) E35),
        (U_atom E 36 (si_P A z) E36) by lia.
      cbn [zalu_raw]. rewrite (zcanon_id (b0 + 8 + x)) by (unfold M64; lia).
      rewrite zcanon_id by (unfold M64; lia).
      unfold si_D, si_P. rewrite (Z.mod_small (z - 1) (2 ^ 32)) by lia. lia. }
    pose proof (st_ok_add_alias rsegs E _ _ si_aP7 (SOff 36 0) HS HaP7) as HS'. clear HS. rename HS' into HS.
    assert (HaP23 : sv_denot E si_aP23 = sv_denot E (SOff 36 0)).
    { apply U_inj. unfold si_aP23.
      rewrite !U_SAlu, (U_atom E 23 (b0 + 8) E23), (U_atom E 24 x E24), (U_atom E 35 (si_D z) E35),
        (U_atom E 36 (si_P A z) E36) by lia.
      cbn [zalu_raw]. rewrite (zcanon_id (b0 + 8 + x)) by (unfold M64; lia).
      rewrite zcanon_id by (unfold M64; lia).
      unfold si_D, si_P. rewrite (Z.mod_small (z - 1) (2 ^ 32)) by lia. lia. }
    pose proof (st_ok_add_alias rsegs E _ _ si_aP23 (SOff 36 0) HS HaP23) as HS'. clear HS. rename HS' into HS.
    si_run. si_mem.
    si_last Hl.
    * (* m + 1 < n_ent: 0x82c0c to the head 0x82b70, `bnez a0` on the key value *)
      si_run. si_mem.
      si_branch Hb;
        rewrite branch_ne_U, (si_and_U E A lb E32 ltac:(lia) ltac:(lia) E37 Hlb), (U_lit E 0) in Hb by lia.
      -- (* taken: the byte is NUL, a key; to KM 0x82c40 *)
         assert (Hlb0 : lb = 0).
         { destruct (Z.eq_dec lb 0) as [Hl0|Hne]; [exact Hl0|].
           rewrite (proj2 (Z.eqb_neq lb 0) Hne) in Hb. cbv in Hb. discriminate Hb. }
         assert (Hk : si_key t z lb = true).
         { unfold si_key. rewrite Hty, Hlb0. replace (1 <=? z) with true by (symmetry; apply Z.leb_le; lia).
           reflexivity. }
         si_run_to RSB_KM. si_mem. apply SRr_ret. right. right.
         split; [apply Z.ltb_lt in Hl; exact Hl|].
         split; [exact Hk|].
         si_post_intro.
         lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
           unfold si_KM_R; rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
         split.
         { si_sv.
           rewrite denot_lit_U. unfold w64. f_equal.
           rewrite (si_and_U E A lb E32 ltac:(lia) ltac:(lia) E37 Hlb), Hlb0. reflexivity. }
         repeat split; si_adv.
      -- (* not taken: the byte is not NUL, not a key; back to I *)
         assert (Hlb0 : lb <> 0).
         { intros Hl0. subst lb. rewrite Z.eqb_refl in Hb. cbv iota in Hb.
           apply negb_false_iff, Z.eqb_eq in Hb. lia. }
         assert (Hk : si_key t z lb = false).
         { unfold si_key. replace (lb =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hlb0).
           rewrite andb_false_r. reflexivity. }
         si_Ileaf Hk Hl.
    * (* m + 1 >= n_ent: to ABS *)
      si_abs Hl.
Qed.

End d.
End b.

(* ================================ the cuts ================================ *)
Lemma si_key_of : forall e, key_of e = if si_key (e_type e) (e_size e) (last_body_byte e) then Some (cstr (e_body e)) else None.
Proof. intros e. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem rkb_inner_B : rsb_piece_W11a_inner_stmt rsegs B MT.
Proof.
unfold rsb_piece_W11a_inner_stmt. intros cx POST inp at0 m Hst HI HKM HA.
unfold rsb_from_I. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec Hcut.
pose proof Hcut as (Hbase & Hat & Hhz & Hinv & Hrec & [Hat0 Hm] & Hrun).
pose proof Hbase as (Hcore & _ & _ & _ & Hpp & Hwf & _).
pose proof Hcore as (HJ & _ & _ & Hperm & _).
pose proof Hst as (Hpre & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
(* the first block at the cut: its place and its shadow *)
pose proof (Permutation_in _ (Permutation_sym Hperm) Hppin) as Hin2.
pose proof HJ as (HAR & _).
pose proof (al_blocks rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR Hin2) as (_ & Hp4k & Hpc & Happ & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpc, Happ.
pose proof (@ASAN_CEIL_range rc) as [[_ Hceil] _]. unfold ASAN_CEIL in Hceil.
unfold Layout.PP_SIZE in Hpc.
(* entry m of the record *)
pose proof (rkb_nent_le rec Hwf) as Hn32.
pose proof (rkb_ent_wf_nth rec m Hwf Hm) as (Htw & Hbl & Hzw).
unfold rkb_d in Htw, Hbl, Hzw.
assert (Hb : Z.of_nat (length (buf rec)) <= POD_BUF_MAX)
  by (pose proof (buf_header rec Hwf) as (_ & _ & _ & HL); unfold POD_BUF_MAX; lia).
assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) (ents rec)).
{ eapply Forall_impl; [|exact (rkb_ents_wf rec Hwf)]. intros e (_ & He & Hz). lia. }
pose proof (rtmb_pp_ent rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec) (corrupt rec)
  Hb Hn32 Hs (w_H W2) mem2 (q_pp (x_e cx)) m Hpp Hm) as Hent.
pose proof (length_ent_mem (nth m (ents rec) (Ent 0 0 [])) ltac:(lia)) as HL104.
pose proof (rtmb_bytes_field rsegs _ _ _ _ 0 4 _ Hent (si_slice_type _) ltac:(lia)) as Vt.
pose proof (rtmb_bytes_field rsegs _ _ _ _ 4 4 _ Hent (si_slice_size _) ltac:(lia)) as Vz.
pose proof (rtmb_bytes_byte rsegs _ _ _ _ (8 + Z.to_nat (e_size (nth m (ents rec) (Ent 0 0 [])) - 1)) Hent
  ltac:(lia)) as Vb.
rewrite si_nth_body in Vb.
set (A := q_pp (x_e cx) + 0x4014 + 104 * Z.of_nat m).
replace (q_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat 0) with A in Vt
  by (unfold A, OFF_ENT, ENT_SIZE; lia).
replace (q_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat 4) with (A + 4) in Vz
  by (unfold A, OFF_ENT, ENT_SIZE; lia).
replace (q_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat (8 + Z.to_nat (e_size (nth m (ents rec) (Ent 0 0 [])) - 1)))
  with (si_P A (e_size (nth m (ents rec) (Ent 0 0 [])))) in Vb by (unfold A, si_P, OFF_ENT, ENT_SIZE; lia).
assert (HRA : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (A - 4) 112).
{ apply (rtmb_blk_ra rsegs B ly2 S2 W2 mem2 md2 (q_pp (x_e cx)) Layout.PP_SIZE (A - 4) 112 HAR Hin2);
  [| rewrite Hrq]; unfold A, Layout.PP_SIZE; lia. }
(* the registers at I *)
unfold rsb_at_cx in Hat.
pose proof (skb_at_get _ _ _ _ _ 18 (q_pp (x_e cx) + 0x4014) Hat ltac:(si_in)) as R18.
pose proof (skb_at_get _ _ _ _ _ 17 (q_pp (x_e cx) + 0x4018) Hat ltac:(si_in)) as R17.
pose proof (skb_at_get _ _ _ _ _ 7 (q_pp (x_e cx) + 0x401c) Hat ltac:(si_in)) as R7.
pose proof (skb_at_get _ _ _ _ _ 23 (q_pp (x_e cx) + 0x401c) Hat ltac:(si_in)) as R23.
pose proof (skb_at_get _ _ _ _ _ 27 (Z.lnot (q_pp (x_e cx) + 0x4014)) Hat ltac:(si_in)) as R27.
pose proof (skb_at_get _ _ _ _ _ 28 8 Hat ltac:(si_in)) as R28.
pose proof (skb_at_get _ _ _ _ _ 26 (Z.of_nat (length (ents rec))) Hat ltac:(si_in)) as R26.
pose proof (skb_at_get _ _ _ _ _ 20 SHADOW_OFF Hat ltac:(si_in)) as R20.
pose proof (skb_at_get _ _ _ _ _ 12 (Z.of_nat m) Hat ltac:(si_in)) as R12.
pose proof (skb_at_get _ _ _ _ _ 22 (Z.of_nat m) Hat ltac:(si_in)) as R22.
pose proof (skb_at_get _ _ _ _ _ 24 (104 * Z.of_nat m) Hat ltac:(si_in)) as R24.
pose proof (skb_at_get _ _ _ _ _ 13 (Z.max (Z.of_nat at0) 33) Hat ltac:(si_in)) as R13.
pose proof (skb_at_get _ _ _ _ _ 14 (Z.lnot (q_pp (x_e cx) + 0x401c) - 104 * Z.of_nat m) Hat ltac:(si_in)) as R14.
unfold rsb_at in Hat. apply Forall_app in Hat as [Hscan _].
fold (rsb_at rsegs (w_H W2) mem2 regs2 (x_e cx) (rsb_L_scan rsegs cx rec)) in Hscan.
(* the same registers in si_blk's form *)
assert (G17 : getr regs2 (Z_to_bv 5 17) = w64 (q_pp (x_e cx) + 0x4014 + 4)) by (rewrite R17; f_equal; lia).
assert (G7 : getr regs2 (Z_to_bv 5 7) = w64 (q_pp (x_e cx) + 0x4014 + 8)) by (rewrite R7; f_equal; lia).
assert (G23 : getr regs2 (Z_to_bv 5 23) = w64 (q_pp (x_e cx) + 0x4014 + 8)) by (rewrite R23; f_equal; lia).
assert (G27 : getr regs2 (Z_to_bv 5 27) = w64 (2 ^ 64 - 1 - (q_pp (x_e cx) + 0x4014))).
{ rewrite R27. apply si_w64_add. pose proof (Z.add_lnot_diag (q_pp (x_e cx) + 0x4014)). lia. }
assert (G14 : getr regs2 (Z_to_bv 5 14) = w64 (2 ^ 64 - 9 - (q_pp (x_e cx) + 0x4014) - 104 * Z.of_nat m)).
{ rewrite R14. apply si_w64_add. pose proof (Z.add_lnot_diag (q_pp (x_e cx) + 0x401c)). lia. }
assert (G13 : getr regs2 (Z_to_bv 5 13) = w64 33) by (rewrite R13; f_equal; lia).
(* the turn *)
eapply SRr_bind.
{ apply (si_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_pp (x_e cx) + 0x4014) (104 * Z.of_nat m) A
    (e_type (nth m (ents rec) (Ent 0 0 []))) (e_size (nth m (ents rec) (Ent 0 0 [])))
    (last_body_byte (nth m (ents rec) (Ent 0 0 []))) (Z.of_nat m) (Z.of_nat (length (ents rec)))
    HJ R18 G17 G7 G23 R24 G27 G14 G13 R12 R22 R26 R28 R20);
  try assumption; try (unfold A; lia).
  - apply rtmb_byte_range.
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, Layout.PP_SIZE, A in *. lia. }
intros W3 c3 _ [(Hl & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)
  | [(Hl & Hkey & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR) | (Hl & Hkey & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR)]].
- (* ABS: entry m is the last one, the answer is (None, 0) *)
  assert (Hlen : (length (ents rec) <= S m)%nat) by lia.
  assert (HE0 : rsb_E0 rec = (None, 0)) by exact (rkb_inv_last rec at0 m Hinv Hat0 Hm Hlen Hrun).
  pose proof Hrec as (_ & _ & _ & Hsnd & Hfst).
  rewrite HE0 in Hsnd, Hfst. cbn [fst snd] in Hsnd, Hfst.
  pose proof (skb_at_keep _ _ regs2 regs3 _ (rsb_L_scan rsegs cx rec) si_kept_regs Hk3
    ltac:(vm_compute; reflexivity) Hscan) as Hscan3.
  apply (HA fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact (skb_chk_base B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
    ltac:(intros r Hr; apply Hk3; destruct Hr as [->|[->| ->]]; si_kin))|].
  split.
  { unfold rsb_at_cx. unfold rsb_L_scan in Hscan3. rewrite Hsnd in Hscan3.
    apply (skb_at_sub _ _ _ _ _ _ Hscan3). intros y Hy. unfold rsb_L_chk, rsb_Hc in Hy |- *. cbn [In app] in Hy |- *.
    repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy. }
  split; [exact Hhz|]. split; assumption.
- (* I at m + 1: entry m is not a key *)
  destruct HR as (Q12 & Q22 & Q24 & Q14).
  assert (Hk : key_of (nth m (ents rec) (Ent 0 0 [])) = None) by (rewrite si_key_of, Hkey; reflexivity).
  pose proof (skb_at_keep _ _ regs2 regs3 _ (rsb_L_scan rsegs cx rec) si_kept_regs Hk3
    ltac:(vm_compute; reflexivity) Hscan) as Hscan3.
  apply (HI fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact (skb_chk_base B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
    ltac:(intros r Hr; apply Hk3; destruct Hr as [->|[->| ->]]; si_kin))|].
  split.
  { unfold rsb_at_cx, rsb_at. apply Forall_app. split; [exact Hscan3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rt_at fst snd].
    - rewrite Q12. f_equal. lia.
    - rewrite Q22. f_equal. lia.
    - rewrite Q24. f_equal. lia.
    - rewrite (Hk3 (Z_to_bv 5 13) ltac:(si_kin)). exact R13.
    - rewrite Q14. symmetry. apply si_w64_add. pose proof (Z.add_lnot_diag (q_pp (x_e cx) + 0x401c)). lia. }
  split; [exact Hhz|]. split; [exact Hinv|]. split; [exact Hrec|].
  split; [lia|].
  intros q Hq. destruct (Nat.eq_dec q m) as [->|Hqm]; [exact Hk | apply Hrun; lia].
- (* KM: entry m is a key, entry m + 1 its value *)
  destruct HR as (Q10 & Q12 & Q22 & Q24).
  assert (Hk : key_of (nth m (ents rec) (Ent 0 0 [])) = Some (cstr (e_body (nth m (ents rec) (Ent 0 0 [])))))
    by (rewrite si_key_of, Hkey; reflexivity).
  pose proof (skb_at_keep _ _ regs2 regs3 _ (rsb_L_scan rsegs cx rec) si_kept_regs Hk3
    ltac:(vm_compute; reflexivity) Hscan) as Hscan3.
  apply (HKM fx2 ly2 S2 W2 regs3 mem2 md3 rec (cstr (e_body (nth m (ents rec) (Ent 0 0 []))))).
  split; [exact (skb_chk_base B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
    ltac:(intros r Hr; apply Hk3; destruct Hr as [->|[->| ->]]; si_kin))|].
  split.
  { unfold rsb_at_cx, rsb_at. apply Forall_app. split; [exact Hscan3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rt_at fst snd].
    - rewrite Q10. unfold A. f_equal. lia.
    - exact Q12.
    - exact Q22.
    - rewrite Q24. f_equal. lia. }
  split; [exact Hhz|]. split; [exact Hinv|]. split; [exact Hrec|].
  split; [lia|]. split; [lia|]. split; [exact Hrun | exact Hk].
Qed.
End e.
End c.

Print Assumptions rkb_inner_B.
