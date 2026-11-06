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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 561 of its 611 lines of code are new or changed and 419 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3bScan.v at 42ff422eb80 (image A's
   twin of this piece, same unit; itself from proofs/reac-pw/fuzz_role/lib/A/RPgScanInner.v at e39c26ea588): the
   prefix hs_ -> hcu_, image A's code 0x830a0 .. 0x83164 replaced by image B's 0x83190 .. 0x8325c (B's scan head
   is rotated - it carries the previous entry's answer in s7 and leaves to the key at its own pc - its entry
   address is one atom plus the offset 104 m instead of five advancing registers, its three UBSan trap branches
   are decided by the atom ranges, and its key test is branchless: `snez`, `addi -1`, `and`), the cut rebuilt over
   lib/AU/HPgSegM.v's hqu_cut_SCAN / hqu_cut_SCANF / hqu_cut_KEY / hqu_cut_RC and lib/AU/HPgBM3bBase.v. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, the same loaded bytes except .note.gnu.build-id): the pieces "one turn
   of the scan" and "the scan head's leaving arm" of the walk of LLVMFuzzerTestOneInput, lib/AU/HPgSegM.v
   hqu_piece_M3b_scan_stmt and hqu_piece_M3b_scanf_stmt. Proves no function (kind: segment lemma).

   THE CODE (SCAN 0x83190 .. 0x8325c, the inlined pod_next_pair's loop with pod_string inlined, pod.h:90-96 and
   :134-142). At the examining state s7 = 0, s5 = 8, a2 = s2 = m, s8 = 104 m, a3 = n_ent, a4 = 33, a5 = the one's
   complement of &ent[m].body, t0 = &ent[0], t1 = &ent[0].size, t2 = the one's complement of &ent[0], t3 = t4 =
   &ent[0].body, s11 = the shadow offset:
     0x83190  bnez s7,0x83260      s7 = 0 here: not taken (the leaving arm is the second piece)
     0x83194  beq a4,s2,0x83a14    the entry-index trap: 33 <> m
     0x83198  bltu t2,s8,0x83a14   the pointer trap: &ent[0] + 104 m does not wrap
     0x8319c  add a0,t0,s8         a0 := &ent[m] = A
     0x831a0 .. 0x831ac            the instrumented check of the 4-byte read at A (slow block 0x83234)
     0x831b0  lw a1,0(a0)          a1 := ent[m].type
     0x831b4  bne a1,s5,0x83218    not the String type: not a key
     0x831b8  add a1,t1,s8         a1 := A + 4
     0x831bc .. 0x831c8            its instrumented check (slow block 0x83244)
     0x831cc  lw a0,4(a0)          a0 := ent[m].size
     0x831d0  beqz a0,0x83218      size 0: not a key
     0x831d4 .. 0x831dc            a0 := zext32 (size - 1) = D
     0x831e0  bltu a5,a0,0x83a14   the pointer trap: the body's last byte does not wrap
     0x831e4  add a1,s8,a0         a1 := 104 m + D
     0x831e8  add a6,a1,t3         a6 := A + 8 + D = P
     0x831ec .. 0x831f8            the instrumented check of the byte at P (slow block 0x83254)
     0x831fc  add a1,t4,a1         a1 := P
     0x83200  lbu a0,0(a1)         a0 := the last body byte
     0x83204  add a1,t4,s8         a1 := A + 8, the body
     0x83208  snez a0,a0 ; 0x8320c addi a0,a0,-1 ; 0x83210 and s7,a0,a1
                                   s7 := A + 8 when the byte is NUL, else 0 (no branch)
     0x83214  j 0x8321c
     0x83218  li s7,0              not a key
     0x8321c .. 0x83228            s2 := m + 1, s8 := 104 (m + 1), a2 := m + 1, a5 := a5 - 104
     0x8322c  blt s2,a3,0x83190    m + 1 < n_ent: back to the head
     0x83230  j 0x83850            else the loop is done: RC
   and the leaving arm is the one instruction 0x83190 `bnez s7,0x83260` at s7 = &ent[m].body <> 0, which goes to
   KEY 0x83260. No store and no call: the turn writes no byte and changes no float register.

   HOW. hcu_blk is the turn as a block lemma over the machine state at SCAN (lib/Reusable: the token engine
   YCbn.v, the journal YCbq.v), stated for any float state. Its entry state has the registers as atoms, with s7,
   s5, a4 pinned to 0, 8 and 33 and s2 pinned to a2's atom, and six more atoms: A = &ent[m] (32), the type t
   (33), the size z (34), D = (z - 1) mod 2 ^ 32 (35), P = A + 8 + max (z - 1, 0) (36) and the byte lb at P (37).
   Alias facts make every address the code computes an atom plus a constant: t0 + s8 and t1 + s8 are A and A + 4,
   t4 + s8 is A + 8, the zero extension of size - 1 is D, and (added once size <> 0 is known, when D = z - 1)
   (s8 + D) + t3 and t4 + (s8 + D) are P. Two read-only regions hold the two words at A and the byte at P. The
   shadow base is s11 (atom 27), and the two shadow entries [A - 4, A + 108) and [P, P + 8) cover the 8 bytes
   from each check's address, so the engine reads each shadow byte as 0 and decides each `bnez` not taken (the
   entries are paid from the pp block's shadow, HPgMem.hm_blk_ra). The engine decides the three trap branches
   from the atom ranges and splits the three it cannot decide (the type, the size, m + 1 < n_ent). hbu_scan_B
   reads SCAN's cut, reads the three fields out of the pp block's image (HPgMem.hm_pp_ent), runs hcu_blk at the
   run's own float state, and rebuilds the cut of the arm: RC (no entry is left: HPgBM3bBase.hbu_fold_last),
   SCANF at m (the entry is a key: the three tests are Accessors.key_of's three conjuncts) or SCAN at m + 1.
   hbu_scanf_B runs the single instruction of the leaving arm and rebuilds the KEY cut. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Spa Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgBM3bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ================================ the code table and the entry state ================================ *)
(* the 52 words 0x83190 .. 0x8325c (the three slow blocks included); the end pcs SCAN 0x83190 is its first word,
   KEY 0x83260 and RC 0x83850 lie outside it *)
Definition hcu_tbl : ctable := build_table rsegs HQU_SCAN 52 TEmpty.
Lemma hcu_tbl_ok : table_ok rsegs hcu_tbl.
Proof. apply build_table_ok0. unfold HQU_SCAN. lia. Qed.

(* the registers the turn does not write and the engine still holds as their own atom: all but a0, a1, a2, a5,
   a6, a7, s2, s7, s8 (written) and a4, s5 (pinned to the literals 33 and 8 at the entry, so they are read back
   from the turn's post instead) *)
Definition hcu_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 19; 20; 22; 25; 26; 27; 28; 29; 30; 31].

(* the shadow base: register s11 (atom 27) holds the shadow offset *)
Definition HCUSB : Z := 0x7fff8000.
Definition HCUBx : sv := SOff 27 0.
Definition HCUBspan : Z * Z := (HCUSB, HCUSB + 2 ^ 44 - 1).

(* the two read-only regions: the type and size words at A (atom 32), the byte at P (atom 36) *)
Definition hcu_R1 : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))].
Definition hcu_R2 : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
(* the zero extension of size - 1, in the form the engine builds for 0x831d4 .. 0x831dc *)
Definition hcu_zx : sv :=
  SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 32)) (SLit (-4294967296))) (SLit 32).
Definition hcu_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 5 0) (SOff 24 0), SOff 32 0);
    (SAlu ALU_ADD (SOff 6 0) (SOff 24 0), SOff 32 4);
    (SAlu ALU_ADD (SOff 29 0) (SOff 24 0), SOff 32 8);
    (hcu_zx, SOff 35 0) ].
(* added once size <> 0 is known, when D = z - 1 *)
Definition hcu_aP1 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 24 0) (SOff 35 0)) (SOff 28 0).
Definition hcu_aP2 : sv := SAlu ALU_ADD (SOff 29 0) (SAlu ALU_ADD (SOff 24 0) (SOff 35 0)).
Definition hcu_aP' : sv := SOff 36 0.
Definition hcu_facts : facts :=
  mkFacts [ (5%nat, mkAF 0x4014 (2 ^ 47) 0); (6%nat, mkAF 0x4018 (2 ^ 47) 0);
            (7%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0);
            (12%nat, mkAF 0 31 0); (13%nat, mkAF 1 32 0);
            (15%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0);
            (24%nat, mkAF 0 3224 0);
            (27%nat, mkAF HCUSB HCUSB 0);
            (28%nat, mkAF 0x401c (2 ^ 47) 0); (29%nat, mkAF 0x401c (2 ^ 47) 0);
            (32%nat, mkAF 0x4014 (2 ^ 47 - 0x200) 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0);
            (34%nat, mkAF 0 45 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
            (36%nat, mkAF 0x401c (2 ^ 47 - 0x100) 0); (37%nat, mkAF 0 255 0) ]
          [] hcu_alias.
Definition hcu_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 23) (SLit 0)) (Z_to_bv 5 21) (SLit 8))
            (Z_to_bv 5 14) (SLit 33)) (Z_to_bv 5 18) (SOff 12 0).
Definition hcu_ss0 : sstate := mkSS HQU_SCAN hcu_regs [hcu_R1; hcu_R2] None hcu_facts.
Definition hcu_SH : list shent := [mkSHE 32 (-4) 108; mkSHE 36 0 8].
(* the six atoms after the registers *)
Definition hcu_D (z : Z) : Z := (z - 1) mod 2 ^ 32.
Definition hcu_P (A z : Z) : Z := A + 8 + Z.of_nat (Z.to_nat (z - 1)).
Definition hcu_extra (A t z lb : Z) : list word :=
  [w64 A; w64 t; w64 z; w64 (hcu_D z); w64 (hcu_P A z); w64 lb].
(* the three tests of pod_string *)
Definition hcu_key (t z lb : Z) : bool := (t =? 8) && (1 <=? z) && (lb =? 0).

(* ================================ arithmetic ================================ *)
Lemma hcu_zx_U : forall E z, ew E 34 = Z_to_bv 64 z -> 0 <= z <= 45 -> U E hcu_zx = hcu_D z.
Proof.
intros E z H Hz. unfold hcu_zx, hcu_D.
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

Lemma hcu_sext_U : forall E t, ew E 33 = Z_to_bv 64 t -> 0 <= t < 2 ^ 32 ->
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

Lemma hcu_soff : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.
Lemma hcu_soffz : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.
(* the same without a bound on the atom's value: the engine wraps the sum, so a one's complement works too *)
Lemma hcu_soffm : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c H. cbn [sv_denot]. rewrite H, Z_to_bv_unsigned. unfold w64, bv_wrap, bv_modulus.
cbn [Z.of_N]. apply Z_to_bv64_eq_mod. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
(* the branchless key test of 0x83208 .. 0x83210: `snez a0,a0`, `addi a0,a0,-1`, `and s7,a0,a1` leaves the
   body's address when the last byte is NUL and 0 otherwise *)
Lemma hcu_sel : forall E lb A,
ew E 37 = Z_to_bv 64 lb -> ew E 32 = Z_to_bv 64 A -> 0 <= lb < 256 -> 0 <= A -> A + 8 < 2 ^ 64 ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 37 0)) (SLit (-1))) (SOff 32 8))
= (if lb =? 0 then A + 8 else 0).
Proof.
intros E lb A E37 E32 Hlb HA0 HA1.
rewrite !U_SAlu, !U_SLit, (U_atom E 37 lb E37), (U_atom_off E 32 A 8 E32) by lia.
cbn [zalu_raw]. unfold zcanon, M64.
assert (Em1 : (-1) mod 2 ^ 64 = 2 ^ 64 - 1).
{ rewrite <- (Z.mod_add (-1) 1 (2 ^ 64)) by lia. apply Z.mod_small. lia. }
rewrite Em1, (Z.mod_0_l (2 ^ 64)) by lia.
destruct (Z.ltb_spec 0 lb) as [Hpos|Hzero].
- rewrite (Z.mod_small 1) by lia.
  replace ((1 + (2 ^ 64 - 1)) mod 2 ^ 64) with 0
    by (replace (1 + (2 ^ 64 - 1)) with (1 * 2 ^ 64) by ring; rewrite Z.mod_mul by lia; reflexivity).
  rewrite Z.land_0_l, (Z.mod_0_l (2 ^ 64)) by lia.
  destruct (Z.eqb_spec lb 0); [lia | reflexivity].
- assert (Hz : lb = 0) by lia. subst lb. cbn [Z.eqb].
  rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_l, (Z.mod_small (2 ^ 64 - 1)) by lia.
  replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_comm, Z.land_ones by lia.
  rewrite (Z.mod_small (A + 8)) by lia. apply Z.mod_small. lia.
Qed.

(* ================================ the entry's bytes ================================ *)
Lemma hcu_firstn4 : forall (a b : list byte), length a = 4%nat -> firstn 4 (a ++ b) = a.
Proof. intros a b H. rewrite firstn_app, H, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia. Qed.
Lemma hcu_slice_type : forall e, hm_slice (ent_mem e) 0 4 = Z_to_le_bytes 4 (e_type e).
Proof. intros e. unfold hm_slice, ent_mem. cbn [skipn]. apply hcu_firstn4. apply Cursor.length_le32. Qed.
Lemma hcu_slice_size : forall e, hm_slice (ent_mem e) 4 4 = Z_to_le_bytes 4 (e_size e).
Proof.
intros e. unfold hm_slice, ent_mem. rewrite skipn_app, Cursor.length_le32, Nat.sub_diag, skipn_O.
rewrite skipn_all2 by (rewrite Cursor.length_le32; lia). cbn [app]. apply hcu_firstn4. apply Cursor.length_le32.
Qed.
Lemma hcu_nth_zeros : forall (l : list byte) n k, nth k (l ++ Cursor.zeros n) Cursor.NUL = nth k l Cursor.NUL.
Proof.
intros l n k. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
- apply app_nth1. exact Hk.
- rewrite app_nth2 by exact Hk. rewrite (nth_overflow l) by exact Hk. unfold Cursor.zeros. apply nth_repeat.
Qed.
Lemma hcu_nth_body : forall e k, nth (8 + k) (ent_mem e) (Z_to_bv 8 0) = nth k (e_body e) Cursor.NUL.
Proof.
intros e k. change (Z_to_bv 8 0) with Cursor.NUL. unfold ent_mem.
rewrite app_nth2 by (rewrite Cursor.length_le32; lia). rewrite Cursor.length_le32.
rewrite app_nth2 by (rewrite Cursor.length_le32; lia). rewrite Cursor.length_le32.
replace (8 + k - 4 - 4)%nat with k by lia. apply hcu_nth_zeros.
Qed.
Lemma hcu_key_of : forall e,
key_of e = if hcu_key (e_type e) (e_size e) (last_body_byte e) then Some (Cursor.cstr (e_body e)) else None.
Proof. intros e. reflexivity. Qed.

(* ================================ the run tactics ================================ *)
Ltac hcu_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok hcu_tbl_ok HS HJ SHOK HCUBspan; [awr_ok_tac | ] end.
Ltac hcu_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok hcu_tbl_ok HS HJ SHOK HCUBspan pc; [awr_ok_tac | ] end.
Ltac hcu_branch Hc := lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok hcu_tbl_ok HS SHOK HCUBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* a register the turn advanced: SOff n c over the atom n, whose value En gives *)
Ltac hcu_adv :=
hbu_sv;
lazymatch goal with |- sv_denot _ (SOff ?n ?c) = w64 ?v =>
  lazymatch goal with En : ew _ n = Z_to_bv 64 ?v0 |- _ =>
    rewrite (hcu_soffm _ n v0 c En); unfold w64; f_equal; lia end end.
Ltac hcu_lit := hbu_sv; cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* what the turn leaves at the scan's head (the answer register s7 is A + 8 for a key, else 0) *)
Definition hcu_RR (A NB5 i : Z) (key : bool) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 18) = w64 (i + 1) /\ getr regs2 (Z_to_bv 5 12) = w64 (i + 1) /\
getr regs2 (Z_to_bv 5 24) = w64 (104 * (i + 1)) /\
getr regs2 (Z_to_bv 5 15) = w64 (NB5 - 104) /\
getr regs2 (Z_to_bv 5 21) = w64 8 /\ getr regs2 (Z_to_bv 5 14) = w64 33 /\
getr regs2 (Z_to_bv 5 23) = w64 (if key then A + 8 else 0).

Lemma hcu_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(E0 i nent t z lb : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 23) = w64 0 -> getr regs (Z_to_bv 5 21) = w64 8 ->
getr regs (Z_to_bv 5 14) = w64 33 -> getr regs (Z_to_bv 5 18) = w64 i ->
getr regs (Z_to_bv 5 12) = w64 i -> getr regs (Z_to_bv 5 13) = w64 nent ->
getr regs (Z_to_bv 5 24) = w64 (104 * i) ->
getr regs (Z_to_bv 5 5) = w64 E0 -> getr regs (Z_to_bv 5 6) = w64 (E0 + 4) ->
getr regs (Z_to_bv 5 28) = w64 (E0 + 8) -> getr regs (Z_to_bv 5 29) = w64 (E0 + 8) ->
getr regs (Z_to_bv 5 7) = w64 (-1 - E0) ->
getr regs (Z_to_bv 5 15) = w64 (-1 - (E0 + 104 * i + 8)) ->
getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
0 <= i <= 31 -> 1 <= nent <= 32 -> 0x4014 <= E0 -> E0 + 19744 <= 2 ^ 47 ->
0 <= t < 2 ^ 32 -> 0 <= z <= 45 -> 0 <= lb < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) (E0 + 104 * i) 4 t ->
val_mem rsegs (mrestrict (w_H W) memc) (E0 + 104 * i + 4) 4 z ->
val_mem rsegs (mrestrict (w_H W) memc) (hcu_P (E0 + 104 * i) z) 1 lb ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (E0 + 104 * i - 4) 112 ->
(forall a, E0 + 104 * i - 4 <= a < E0 + 104 * i + 108 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs HQU_SCAN regs memc mdc)
(fun W2 c2 =>
 (nent <= i + 1 /\ hbu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RC hcu_kept
                     (fun _ => True) W2 c2) \/
 (i + 1 < nent /\ hbu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_SCAN hcu_kept
                     (hcu_RR (E0 + 104 * i) (-1 - (E0 + 104 * i + 8)) i (hcu_key t z lb)) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E0 i nent t z lb HJ
  H23 H21 H14 H18 H12 H13 H24 H5 H6 H28 H29 H7 H15 H27 Hi Hn HE1 HE2 Ht Hz Hlb Vt Vz Vb HRA Happ.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hcu_extra (E0 + 104 * i) t z lb) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E5 : ew (Ereg regs ex) 5 = Z_to_bv 64 E0) by (rewrite (EA 5%nat (Z_to_bv 5 5) eq_refl); exact H5).
assert (E6 : ew (Ereg regs ex) 6 = Z_to_bv 64 (E0 + 4)) by (rewrite (EA 6%nat (Z_to_bv 5 6) eq_refl); exact H6).
assert (E7 : ew (Ereg regs ex) 7 = Z_to_bv 64 (-1 - E0)) by (rewrite (EA 7%nat (Z_to_bv 5 7) eq_refl); exact H7).
assert (E12 : ew (Ereg regs ex) 12 = Z_to_bv 64 i) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E13 : ew (Ereg regs ex) 13 = Z_to_bv 64 nent) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E15 : ew (Ereg regs ex) 15 = Z_to_bv 64 (-1 - (E0 + 104 * i + 8)))
  by (rewrite (EA 15%nat (Z_to_bv 5 15) eq_refl); exact H15).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 (104 * i)) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E28 : ew (Ereg regs ex) 28 = Z_to_bv 64 (E0 + 8)) by (rewrite (EA 28%nat (Z_to_bv 5 28) eq_refl); exact H28).
assert (E29 : ew (Ereg regs ex) 29 = Z_to_bv 64 (E0 + 8)) by (rewrite (EA 29%nat (Z_to_bv 5 29) eq_refl); exact H29).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (E0 + 104 * i)) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 t) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 z) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 (hcu_D z)) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew (Ereg regs ex) 36 = Z_to_bv 64 (hcu_P (E0 + 104 * i) z))
  by (subst ex; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew (Ereg regs ex) 37 = Z_to_bv 64 lb) by (subst ex; exact (ew_Ereg_extra regs _ 5)).
assert (HD : 0 <= hcu_D z < 2 ^ 32) by (unfold hcu_D; apply Z.mod_pos_bound; lia).
assert (HP : E0 + 104 * i + 8 <= hcu_P (E0 + 104 * i) z <= E0 + 104 * i + 52) by (unfold hcu_P; lia).
assert (M7 : (-1 - E0) mod 2 ^ 64 = 2 ^ 64 - 1 - E0).
{ rewrite <- (Z.mod_add (-1 - E0) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
assert (M15 : (-1 - (E0 + 104 * i + 8)) mod 2 ^ 64 = 2 ^ 64 - 1 - (E0 + 104 * i + 8)).
{ rewrite <- (Z.mod_add (-1 - (E0 + 104 * i + 8)) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
assert (HS : st_ok rsegs (Ereg regs ex) hcu_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQU_SCAN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hcu_ss0. apply (entry_st_ok_full rsegs).
  - unfold hcu_regs.
    apply regs_ok_rereg;
      [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |]
        | reflexivity |] | reflexivity |] | reflexivity |].
    + rewrite H23. reflexivity.
    + rewrite H21. reflexivity.
    + rewrite H14. reflexivity.
    + rewrite H18. rewrite hbu_denot0, E12. reflexivity.
  - vm_compute. reflexivity.
  - unfold hcu_R1, hcu_R2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ (E0 + 104 * i) 0 4 (SOff 33 0) t);
          [rewrite hbu_denot0; exact E33 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vt.
      * apply (chunk_ok_val rsegs _ _ (E0 + 104 * i) 4 4 (SOff 34 0) z);
          [rewrite hbu_denot0; exact E34 | cbn; lia | cbn; lia |].
        exact Vz.
    + rewrite E36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (hcu_P (E0 + 104 * i) z) 0 1 (SOff 37 0) lb);
        [rewrite hbu_denot0; exact E37 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, hcu_R1, hcu_R2. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E32, E36, !unsigned_lit_small by lia. left. lia.
  - split; [|split; [exact I|]].
    + cbn [hcu_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E5, E6, E7, E12, E13, E15, E24, E27, E28, E29, E32, E33, E34, E35, E36, E37.
      rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold hcu_P, hcu_D, HCUSB, SHADOW_OFF in *.
      rewrite M7, M15. rewrite !(Z.mod_small _ (2 ^ 64)) by lia. repeat split; try lia.
    + cbn [hcu_facts f_alias alias_ok hcu_alias]. unfold hcu_zx.
      repeat split; apply U_inj.
      * rewrite U_SAlu, (U_atom _ 5 E0 E5), (U_atom _ 24 (104 * i) E24), (U_atom _ 32 (E0 + 104 * i) E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 6 (E0 + 4) E6), (U_atom _ 24 (104 * i) E24),
          (U_atom_off _ 32 (E0 + 104 * i) 4 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 29 (E0 + 8) E29), (U_atom _ 24 (104 * i) E24),
          (U_atom_off _ 32 (E0 + 104 * i) 8 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * fold hcu_zx. rewrite (hcu_zx_U _ z E34 Hz), (U_atom _ 35 (hcu_D z) E35) by lia. reflexivity. }
assert (U27 : U (Ereg regs ex) HCUBx = SHADOW_OFF) by (apply U_atom; [exact E27 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs HCUBx hcu_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, hcu_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H W) memc _ HCUBx 32 (E0 + 104 * i - 4) 112 (E0 + 104 * i) (-4) 108 HRA U27);
      [| lia | lia |].
    + apply U_atom; [exact E32 | lia].
    + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia.
  - apply (shent_ok_of_range rsegs (w_H W) memc _ HCUBx 36 (E0 + 104 * i - 4) 112
      (hcu_P (E0 + 104 * i) z) 0 8 HRA U27); [| lia | lia |].
    + apply U_atom; [exact E36 | lia].
    + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HQU_SCAN) with (Z_to_bv 64 HQU_SCAN).
hcu_run. hbu_mem.
hcu_branch Hty; rewrite branch_ne_U, U_lit, (hcu_sext_U E t E33 Ht) in Hty by lia.
- (* taken: not a String *)
  apply negb_true_iff in Hty.
  assert (Hk : hcu_key t z lb = false) by (unfold hcu_key; rewrite Hty; reflexivity).
  hcu_run. hbu_mem.
  hcu_branch Hl; rewrite (hcu_soffz E 12 i 1 E12), hbu_denot0, E13, hbu_blt in Hl by lia.
  + hcu_run_to HQU_SCAN. hbu_mem. apply SRr_ret; right.
    split; [apply Z.ltb_lt in Hl; lia|]. hbu_post_intro B hcu_kept.
    unfold hcu_RR. rewrite Hk.
    lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
      rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
    split; [hcu_adv|]. split; [hcu_adv|]. split; [hcu_adv|]. split; [hcu_adv|].
      split; [hcu_lit|]. split; [hcu_lit|]. hcu_lit.
  + hcu_run_to HQU_RC. hbu_mem. apply SRr_ret; left.
    split; [apply Z.ltb_ge in Hl; lia|]. hbu_post_intro B hcu_kept. exact I.
- apply negb_false_iff in Hty.
  hcu_run. hbu_mem.
  hcu_branch Hsz; rewrite branch_eq_U, (U_atom E 34 z E34), U_lit in Hsz by lia.
  + (* size 0: not a key *)
    assert (Hk : hcu_key t z lb = false).
    { unfold hcu_key. replace (1 <=? z) with false by (symmetry; apply Z.leb_gt; apply Z.eqb_eq in Hsz; lia).
      rewrite andb_false_r. reflexivity. }
    hcu_run. hbu_mem.
    hcu_branch Hl; rewrite (hcu_soffz E 12 i 1 E12), hbu_denot0, E13, hbu_blt in Hl by lia.
    * hcu_run_to HQU_SCAN. hbu_mem. apply SRr_ret; right.
      split; [apply Z.ltb_lt in Hl; lia|]. hbu_post_intro B hcu_kept.
      unfold hcu_RR. rewrite Hk.
      lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
        rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
      split; [hcu_adv|]. split; [hcu_adv|]. split; [hcu_adv|]. split; [hcu_adv|].
      split; [hcu_lit|]. split; [hcu_lit|]. hcu_lit.
    * hcu_run_to HQU_RC. hbu_mem. apply SRr_ret; left.
      split; [apply Z.ltb_ge in Hl; lia|]. hbu_post_intro B hcu_kept. exact I.
  + (* size >= 1: the body's last byte decides the answer without a branch *)
    apply Z.eqb_neq in Hsz.
    assert (HD1 : hcu_D z = z - 1) by (unfold hcu_D; apply Z.mod_small; lia).
    assert (HP1 : hcu_P (E0 + 104 * i) z = E0 + 104 * i + 8 + (z - 1)) by (unfold hcu_P; lia).
    assert (HA1 : sv_denot E hcu_aP1 = sv_denot E hcu_aP').
    { apply U_inj. unfold hcu_aP1, hcu_aP'.
      rewrite !U_SAlu, (U_atom E 24 (104 * i) E24), (U_atom E 35 (hcu_D z) E35),
        (U_atom E 28 (E0 + 8) E28), (U_atom E 36 (hcu_P (E0 + 104 * i) z) E36) by (rewrite ?HP1, ?HD1; lia).
      cbn [zalu_raw]. rewrite HD1, HP1. unfold zcanon, M64.
      rewrite (Z.mod_small (104 * i + (z - 1))) by lia. rewrite Z.mod_small by lia. lia. }
    pose proof (st_ok_add_alias rsegs E _ _ hcu_aP1 hcu_aP' HS HA1) as HS1. clear HS. rename HS1 into HS.
    assert (HA2 : sv_denot E hcu_aP2 = sv_denot E hcu_aP').
    { apply U_inj. unfold hcu_aP2, hcu_aP'.
      rewrite !U_SAlu, (U_atom E 24 (104 * i) E24), (U_atom E 35 (hcu_D z) E35),
        (U_atom E 29 (E0 + 8) E29), (U_atom E 36 (hcu_P (E0 + 104 * i) z) E36) by (rewrite ?HP1, ?HD1; lia).
      cbn [zalu_raw]. rewrite HD1, HP1. unfold zcanon, M64.
      rewrite (Z.mod_small (104 * i + (z - 1))) by lia. rewrite Z.mod_small by lia. lia. }
    pose proof (st_ok_add_alias rsegs E _ _ hcu_aP2 hcu_aP' HS HA2) as HS1. clear HS. rename HS1 into HS.
    assert (Hk : hcu_key t z lb = (lb =? 0)).
    { unfold hcu_key. rewrite Hty. replace (1 <=? z) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    hcu_run. hbu_mem.
    hcu_branch Hl; rewrite (hcu_soffz E 12 i 1 E12), hbu_denot0, E13, hbu_blt in Hl by lia.
    * hcu_run_to HQU_SCAN. hbu_mem. apply SRr_ret; right.
      split; [apply Z.ltb_lt in Hl; lia|]. hbu_post_intro B hcu_kept.
      unfold hcu_RR. rewrite Hk.
      lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
        rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
      split; [hcu_adv|]. split; [hcu_adv|]. split; [hcu_adv|]. split; [hcu_adv|].
      split; [hcu_lit|]. split; [hcu_lit|].
      hbu_sv. rewrite denot_lit_U, (hcu_sel E lb (E0 + 104 * i) E37 E32) by lia. reflexivity.
    * hcu_run_to HQU_RC. hbu_mem. apply SRr_ret; left.
      split; [apply Z.ltb_ge in Hl; lia|]. hbu_post_intro B hcu_kept. exact I.
Qed.

(* ---------------- the leaving arm: the one instruction 0x83190 at s7 <> 0 ---------------- *)
Definition hcf_tbl : ctable := build_table rsegs HQU_SCAN 1 TEmpty.
Lemma hcf_tbl_ok : table_ok rsegs hcf_tbl.
Proof. apply build_table_ok0. unfold HQU_SCAN. lia. Qed.
Definition hcf_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25;
                 26; 27; 28; 29; 30; 31].
Definition hcf_facts : facts := mkFacts [(23%nat, mkAF 1 (2 ^ 47) 0)] [] [].
Definition hcf_ss0 : sstate := mkSS HQU_SCAN sr_atoms [] None hcf_facts.

Lemma hcf_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (S7 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 23) = w64 S7 -> 0 < S7 <= 2 ^ 47 ->
SRr rsegs W (cfg_at rsegs HQU_SCAN regs memc mdc)
(hbu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_KEY hcf_kept (fun _ => True)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs S7 HJ H23 HS7.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 S7) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (HS : st_ok rsegs (Ereg regs ex) hcf_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQU_SCAN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hcf_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [hcf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E23, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite (Z.mod_small S7) by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HQU_SCAN) with (Z_to_bv 64 HQU_SCAN).
aj_run_to_tok hcf_tbl_ok HS HJ SHOK HPgSteps.RTBspan HQU_KEY; [awr_ok_tac | ]. hbu_mem.
apply SRr_ret. hbu_post_intro B hcf_kept. exact I.
Qed.
End d.
End b.

(* ================================ the cuts ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hbu_scan_B : hqu_piece_M3b_scan_stmt rsegs B MT.
Proof.
unfold hqu_piece_M3b_scan_stmt. intros cx POST r ev at0 m HS HSC HSF HRC.
unfold hqu_from_SCAN. intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hf3 & Hlive & [Hat0 Hm] & Hrun & Hx & Hfold).
pose proof Hb3 as (Hcore & _ & _ & _ & Hpp & _).
pose proof Hcore as (HJ & _ & _ & Hperm & _).
pose proof (hbu_start_wf B cx r ev HS) as Hwf.
pose proof (hbu_start_pp B cx r ev HS) as (Hppin & Hal16 & Hp4k & Hpc & Hceil).
pose proof (Permutation_in _ (Permutation_sym Hperm) Hppin) as Hin2.
pose proof HJ as (HAR & _).
pose proof (al_blocks rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR Hin2) as (_ & _ & _ & Happ & _).
assert (Hrq : req_size PP_SIZE = PP_SIZE) by reflexivity. rewrite Hrq in Happ.
pose proof (@alloc_ceiling_val rc) as [[Hc0 Hc1] _].
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
pose proof (proj2 (ents_wf r Hwf)) as Hews.
assert (Hewm : ent_wf (nth m (ents r) (Ent 0 0 []))).
{ rewrite Forall_forall in Hews. apply Hews. apply nth_In. exact Hm. }
destruct Hewm as (Htw & Hbl & Hzw).
assert (Hb : Z.of_nat (length (buf r)) <= POD_BUF_MAX)
  by (pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & HL); unfold POD_BUF_MAX; lia).
assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) (ents r)).
{ eapply Forall_impl; [|exact Hews]. intros e (_ & He & Hz). lia. }
pose proof (hm_pp_ent rsegs (buf r) (is_props r) (has_params r) (params_struct r) (ents r) (corrupt r)
  Hb Hn32 Hs (w_H W2) mem2 (e_pp (x_e cx)) m Hpp Hm) as Hent.
pose proof (length_ent_mem (nth m (ents r) (Ent 0 0 [])) ltac:(lia)) as HL104.
pose proof (hm_bytes_field rsegs _ _ _ _ 0 4 _ Hent (hcu_slice_type _) ltac:(lia)) as Vt.
pose proof (hm_bytes_field rsegs _ _ _ _ 4 4 _ Hent (hcu_slice_size _) ltac:(lia)) as Vz.
pose proof (hm_bytes_byte rsegs _ _ _ _ (8 + Z.to_nat (e_size (nth m (ents r) (Ent 0 0 [])) - 1)) Hent
  ltac:(lia)) as Vb.
rewrite hcu_nth_body in Vb.
replace (e_pp (x_e cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat m) + Z.of_nat 0)
  with (e_pp (x_e cx) + Layout.OFF_ENT + 104 * Z.of_nat m) in Vt
  by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
replace (e_pp (x_e cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat m) + Z.of_nat 4)
  with (e_pp (x_e cx) + Layout.OFF_ENT + 104 * Z.of_nat m + 4) in Vz
  by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
replace (e_pp (x_e cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat m)
         + Z.of_nat (8 + Z.to_nat (e_size (nth m (ents r) (Ent 0 0 [])) - 1)))
  with (hcu_P (e_pp (x_e cx) + Layout.OFF_ENT + 104 * Z.of_nat m) (e_size (nth m (ents r) (Ent 0 0 []))))
  in Vb by (unfold hcu_P, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
assert (HRA : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF
  (e_pp (x_e cx) + Layout.OFF_ENT + 104 * Z.of_nat m - 4) 112).
{ apply (proj1 (hm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (e_pp (x_e cx)) PP_SIZE
    (e_pp (x_e cx) + Layout.OFF_ENT + 104 * Z.of_nat m - 4) 112 HAR Hin2
    ltac:(unfold Layout.OFF_ENT; lia) ltac:(rewrite Hrq; unfold Layout.OFF_ENT, PP_SIZE; lia))). }
(* the registers at SCAN *)
unfold hsu_at_cx in Hat.
pose proof (hbu_at_get _ _ _ _ _ 23 0 Hat ltac:(hbu_in)) as R23.
pose proof (hbu_at_get _ _ _ _ _ 21 8 Hat ltac:(hbu_in)) as R21.
pose proof (hbu_at_get _ _ _ _ _ 14 (Z.max 33 (Z.of_nat at0)) Hat ltac:(hbu_in)) as R14.
pose proof (hbu_at_get _ _ _ _ _ 18 (Z.of_nat m) Hat ltac:(hbu_in)) as R18.
pose proof (hbu_at_get _ _ _ _ _ 12 (Z.of_nat m) Hat ltac:(hbu_in)) as R12.
pose proof (hbu_at_get _ _ _ _ _ 13 (hqu_nent r) Hat ltac:(hbu_in)) as R13.
pose proof (hbu_at_get _ _ _ _ _ 24 (Layout.ENT_SIZE * Z.of_nat m) Hat ltac:(hbu_in)) as R24.
pose proof (hbu_at_get _ _ _ _ _ 5 (e_pp (x_e cx) + Layout.OFF_ENT) Hat ltac:(hbu_in)) as R5.
pose proof (hbu_at_get _ _ _ _ _ 6 (e_pp (x_e cx) + Layout.OFF_ENT + 4) Hat ltac:(hbu_in)) as R6.
pose proof (hbu_at_get _ _ _ _ _ 7 (hqu_not (e_pp (x_e cx) + Layout.OFF_ENT)) Hat ltac:(hbu_in)) as R7.
pose proof (hbu_at_get _ _ _ _ _ 28 (e_pp (x_e cx) + Layout.OFF_ENT + 8) Hat ltac:(hbu_in)) as R28.
pose proof (hbu_at_get _ _ _ _ _ 29 (e_pp (x_e cx) + Layout.OFF_ENT + 8) Hat ltac:(hbu_in)) as R29.
pose proof (hbu_at_get _ _ _ _ _ 15
  (hqu_not (e_pp (x_e cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m)) Hat ltac:(hbu_in)) as R15.
pose proof (hbu_at_get _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(hbu_in)) as R27.
assert (Hat' : hsu_at rsegs (w_H W2) mem2 regs2 (x_e cx)
  (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_loopr rsegs cx ++ hqu_L_t56 rsegs cx)) by hbu_sub Hat.
assert (Hmax : Z.max 33 (Z.of_nat at0) = 33) by lia.
rewrite Hmax in R14.
unfold hqu_not, hqu_nent, Layout.ENT_SIZE in R7, R15, R13, R24.
replace (e_pp (x_e cx) + Layout.OFF_ENT + 8 + 104 * Z.of_nat m)
  with (e_pp (x_e cx) + Layout.OFF_ENT + 104 * Z.of_nat m + 8) in R15 by lia.
assert (Hnent : 1 <= Z.of_nat (length (ents r)) <= 32) by lia.
assert (Hi31 : 0 <= Z.of_nat m <= 31) by lia.
assert (HE1 : 0x4014 <= e_pp (x_e cx) + Layout.OFF_ENT) by (unfold Layout.OFF_ENT; lia).
assert (HE2 : e_pp (x_e cx) + Layout.OFF_ENT + 19744 <= 2 ^ 47)
  by (unfold Layout.OFF_ENT, PP_SIZE in *; lia).
eapply SRr_bind.
{ apply (hcu_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2
    (e_pp (x_e cx) + Layout.OFF_ENT) (Z.of_nat m) (Z.of_nat (length (ents r)))
    (e_type (nth m (ents r) (Ent 0 0 []))) (e_size (nth m (ents r) (Ent 0 0 [])))
    (last_body_byte (nth m (ents r) (Ent 0 0 []))) HJ R23 R21 R14 R18 R12 R13 R24 R5 R6 R28 R29 R7 R15 R27);
  try lia.
  - apply hm_byte_range.
  - exact Vt.
  - exact Vz.
  - exact Vb.
  - exact HRA.
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, Layout.OFF_ENT, PP_SIZE in *. lia. }
intros W3 c3 _ [(Hge & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)
              | (Hlt & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HRR)].
- (* RC: entry m is the last one, so no pair is left *)
  destruct (hbu_fold_last rsegs cx r at0 m cs keys rf Hfold Hat0 Hm ltac:(lia) Hrun) as (-> & -> & ->).
  pose proof (hbu_at_keep _ _ _ _ _ Hat' regs3 hcu_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HRC fx2 ly2 S2 W2 regs3 mem2 md3).
  split.
  { apply (hbu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hcu_kept; hbu_kin. }
  split; [unfold hsu_at_cx; hbu_sub Hat3|].
  split; [exact (proj1 (proj2 Hlive))|].
  split; [exact (hbu_exp_rc rsegs cx r Hlive) | exact Hx].
- destruct HRR as (Q18 & Q12 & Q24 & Q15 & Q21 & Q14 & Q23).
  pose proof (hbu_at_keep _ _ _ _ _ Hat' regs3 hcu_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  destruct (hcu_key (e_type (nth m (ents r) (Ent 0 0 []))) (e_size (nth m (ents r) (Ent 0 0 [])))
                    (last_body_byte (nth m (ents r) (Ent 0 0 [])))) eqn:Hkey.
  + (* a key: the rotated head leaves at the same pc with s7 = &ent[m].body *)
    assert (Hk : key_of (nth m (ents r) (Ent 0 0 []))
                 = Some (Cursor.cstr (e_body (nth m (ents r) (Ent 0 0 [])))))
      by (rewrite hcu_key_of, Hkey; reflexivity).
    apply (HSF fx2 ly2 S2 W2 regs3 mem2 md3 (Cursor.cstr (e_body (nth m (ents r) (Ent 0 0 [])))) cs keys rf).
    split.
    { apply (hbu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
      intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hcu_kept; hbu_kin. }
    split.
    { unfold hsu_at_cx. apply hbu_at_app; split; [hbu_sub Hat3|].
      apply hbu_at_app; split; [hbu_sub Hat3|].
      apply hbu_at_app; split; [hbu_sub Hat3|].
      apply hbu_at_app; split; [hbu_sub Hat3|].
      unfold hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
      - exact Q21.
      - rewrite Q23. unfold w64, hqu_not, Layout.ENT_SIZE. f_equal; lia.
      - exact Q12.
      - exact Q18.
      - rewrite Q24. unfold w64, Layout.ENT_SIZE. f_equal; lia.
      - rewrite Hk3 by (unfold hcu_kept; hbu_kin). unfold hqu_nent. exact R13.
      - rewrite Q14. unfold w64. f_equal; lia.
      - rewrite Q15. unfold w64, hqu_not, Layout.ENT_SIZE. f_equal; lia. }
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|].
    split; [exact Hlive|]. split; [lia|]. split; [lia|].
    split; [unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia|].
    split; [exact Hrun|]. split; [exact Hk|]. split; [exact Hx | exact Hfold].
  + (* not a key: the head examines entry m + 1 *)
    assert (Hk : key_of (nth m (ents r) (Ent 0 0 [])) = None)
      by (rewrite hcu_key_of, Hkey; reflexivity).
    apply (HSC fx2 ly2 S2 W2 regs3 mem2 md3 cs keys rf).
    split.
    { apply (hbu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
      intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hcu_kept; hbu_kin. }
    split.
    { unfold hsu_at_cx. apply hbu_at_app; split; [hbu_sub Hat3|].
      apply hbu_at_app; split; [hbu_sub Hat3|].
      apply hbu_at_app; split; [hbu_sub Hat3|].
      apply hbu_at_app; split; [hbu_sub Hat3|].
      unfold hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
      - exact Q21.
      - exact Q23.
      - rewrite Q12. unfold w64. f_equal; lia.
      - rewrite Q18. unfold w64. f_equal; lia.
      - rewrite Q24. unfold w64, Layout.ENT_SIZE. f_equal; lia.
      - rewrite Hk3 by (unfold hcu_kept; hbu_kin). unfold hqu_nent. exact R13.
      - rewrite Q14. unfold w64. f_equal; lia.
      - rewrite Q15. unfold w64, hqu_not, Layout.ENT_SIZE. f_equal; lia. }
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|].
    split; [exact Hlive|].
    split; [lia|].
    split; [intros q Hq; destruct (Nat.eq_dec q m) as [->|Hqm]; [exact Hk | apply Hrun; lia]|].
    split; [exact Hx | exact Hfold].
Qed.

Theorem hbu_scanf_B : hqu_piece_M3b_scanf_stmt rsegs B MT.
Proof.
unfold hqu_piece_M3b_scanf_stmt. intros cx POST r ev at0 m HS HKEY.
unfold hqu_from_SCANF. intros fx2 ly2 S2 W2 regs2 mem2 md2 kb cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hf3 & Hlive & Hat0 & Hm & Hpos & Hrun & Hkey & Hx & Hfold).
pose proof Hb3 as (Hcore & _).
pose proof Hcore as (HJ & _).
pose proof (hbu_start_wf B cx r ev HS) as Hwf.
pose proof (hbu_start_pp B cx r ev HS) as (_ & _ & Hp4k & Hpc & Hceil).
pose proof (@alloc_ceiling_val rc) as [[Hc0 Hc1] _].
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
unfold hsu_at_cx in Hat.
pose proof (hbu_at_get _ _ _ _ _ 23
  (e_pp (x_e cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m) Hat ltac:(hbu_in)) as R23.
eapply SRr_bind.
{ apply (hcf_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2
    (e_pp (x_e cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m) HJ R23).
  unfold Layout.OFF_ENT, Layout.ENT_SIZE, PP_SIZE in *. lia. }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _).
pose proof (hbu_at_keep _ _ _ _ _ Hat regs3 hcf_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
apply (HKEY fx2 ly2 S2 W2 regs3 mem2 md3 kb cs keys rf).
split.
{ apply (hbu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
  intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hcf_kept; hbu_kin. }
split; [unfold hsu_at_cx; hbu_sub Hat3|].
split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|].
split; [exact Hlive|]. split; [exact Hat0|]. split; [exact Hm|]. split; [exact Hpos|].
split; [exact Hrun|]. split; [exact Hkey|]. split; [exact Hx | exact Hfold].
Qed.
End c.

Print Assumptions hbu_scan_B.
Print Assumptions hbu_scanf_B.
