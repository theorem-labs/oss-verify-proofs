(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 944 of its 983 lines of code are new or changed and 287 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPostArms.v at 8af9cea6f917; ported to image B
   (fuzz_rate.asan-ubsan) over lib/AU's RtPgMemB / RtPgSegB / RtPgStepsB / RtPgPostKB / RtPgPostReqB under the prefix
   wb10a_: image B's code from T = 0x8270c (the cursor in s10 and what is left in t4, the shadow address of &pp->len in
   the cell R+0x170, len read into s6, the B-only divide-by-zero trap 0x82918), len split at the Coq level into 8 and
   9 .. 5440 so that the engine decides `bltu s6,9` and the trap, one run lemma per length class 0 / 1 / 2 / 3 / >= 4
   of what is left (image A: 0, 1 or 2, 3, >= 4) and one for len = 8. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the second half of the post piece of the walk
   of LLVMFuzzerTestOneInput (0x8076c), from the cut T = 0x8270c (lib/AU/RtPgPostKB.v wb10_cut_T) to the head of the
   corruption loop R = 0x82960 (turn 0), the loop's end RT = 0x829fc, or the second request C2 through
   lib/AU/RtPgPostReqB.v (wb10_tail at 0x82a14, wb10_tail8 at 0x82a24): RtPgPostKB.wb10_arms_stmt. Proves no function
   (kind: segment lemma).
   THE CODE (fuzz.h:39-42, pod.h:441-445)
     0x8270c beqz t4 -> 0x82a14                            nothing is left of the input: no corruption
     0x82710 addi a1,s10,1 / li a0,1 / bgeu a0,a1 -> trap  T1 (the cursor does not wrap)
     0x8271c the shadow test of the cursor's byte (bnez -> 0x830fc: andi a2,s10,7; blt a2,a0 back 0x8272c)
     0x8272c lbu a0,0(s10) / andi a0,a0,15 / bne a0,15 -> 0x82a14     c, the corruption's test
     0x8273c ld a0,0x170(s1) / lbu a0,0(a0) / bnez -> 0x83504          the shadow byte of &pp->len
     0x82748 ld s6,0(t2) / li a0,9 / bltu s6,a0 -> 0x82a24             len <= 8: no corruption (s6 = len)
     0x82754 li a0,1 / bne t4,a0 -> 0x827a8; 0x8275c (|r| = 1) a5 = a4 = a6 = 0, j 0x82904 (a1 = s10 + 1)
     0x827a8 T1 (0x827ac), the shadow test of the byte at a1 (0x83250), 0x827c0 lbu a4,0(a1) (b1), a0 = s10 + 2,
             bne t4,2 -> 0x828d8; 0x827d0 (|r| = 2) a5 = a6 = 0, a1 = a0, j 0x82904
     0x828d8 T1 (0x828e0), the shadow test of the byte at a0 (0x832a8), 0x828f4 lbu a6,0(a0) (b2),
             a5 = t4 - 3, a1 = s10 + 3, a6 = b2 << 8
     0x82904 the shadow byte of &pp->len (bnez -> 0x83514), 0x82910 ld a7,0(t2) / addi a7,a7,-8 / beqz a7 -> trap
             (the B-only divide-by-zero test, T8)
     0x8291c beqz a5 -> RT                                 |r| in {1, 2, 3}: no count byte
     0x82920 T1 (0x82928), the shadow test of the byte at a1 (0x83240), 0x8293c lbu a2,0(a1) (n) / andi a2,a2,7 /
             beqz a2 -> RT
     0x82948 .. 0x8295c a3 = 0, a1 = b2 << 8 | b1, a5 = t4 - 4, a4 = a1 remu (len - 8) + 8, a6 = 1: the loop's
             head R at turn 0 (a0 = s10 + 4, a2 = n mod 8, a7 = len - 8)
   The piece writes nothing. Each input read's shadow check can take its second test (the input's last partial
   granule); the engine's token path (lib/Reusable/YCbn.v) follows both outcomes and leaves the obligation that the
   byte is addressable, which the build's input premises give (RtPgPostKB.wb10_input_now); the two reads of the
   shadow byte of &pp->len leave the obligation that the 8 bytes at pp + 0x4000 are addressable (the first block).
   Every trap branch (T1 at 0x82718 / 0x827ac / 0x828e0 / 0x82928, T8 at 0x82918) and every test of t4 is decided
   by the engine from the closed-numeral atom ranges of the entry state: s10 in [1, 2^47 - 1 - m], len in [8, 8] or
   [9, 5440] (len is split at the Coq level), t4 a literal for |r| <= 3 or in [4, 2^63] (or [1, 2^63] for len = 8).
   One engine-run lemma per case: |r| = 0 (wb10a_c0), len = 8 with |r| >= 1 (wb10a_c8), and for len >= 9 |r| = 1
   (wb10a_c1), 2 (wb10a_c2), 3 (wb10a_c3), 4 or more (wb10a_c4), each from one entry state (wb10a_ss); the arms of
   Model.corr_step are wb10a_m_*. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB RtPgStepsB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgPostKB RtPgPostReqB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* ======================================== 1. the entry state at T ========================================
   env slots: 0 .. 31 the registers (t2 = pp + 0x4000 at 7, s1 = R at 9, s4 = K at 20, s10 = the cursor at 26,
   t4 = |r| at 29), then 32 len and 33 .. 36 the next four input bytes (0 past the end). t4 is pinned to a literal
   where the class fixes |r|. Regions: the cell R+0x170 holding the shadow address of &pp->len as the engine's
   shadow expression of atom 7 (so the two `lbu` of it are shadow-token loads), pp->len, and the first m input
   bytes. *)
Definition wb10a_sh : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 7 0) (SLit 3)) (SOff 20 0).
Definition wb10a_sr (t4v : sv) : list sv := sr_set sr_atoms (Z_to_bv 5 29) t4v.
Definition wb10a_rsh : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x170 0x178 0 0 [YP09.mkChunk 0x170 (CVal 8 wb10a_sh)].
Definition wb10a_rlen : YP09.region := YP09.mkRegion (Some 7%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition wb10a_bchunks (m : nat) : list YP09.chunk :=
  map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (33 + i) 0))) (seq 0 m).
Definition wb10a_rin (m : nat) : YP09.region := YP09.mkRegion (Some 26%nat) 0 (Z.of_nat m) 0 0 (wb10a_bchunks m).
Definition wb10a_mem (m : nat) : smem :=
  match m with O => [wb10a_rsh; wb10a_rlen] | S _ => [wb10a_rsh; wb10a_rlen; wb10a_rin m] end.
(* every bound below is a closed numeral once m, lo, hi, llo and lhi are (each use gives numerals) *)
Definition wb10a_G (m : nat) (lo hi llo lhi : Z) : facts :=
  mkFacts [(7%nat, mkAF 4096 WB10_HI 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (26%nat, mkAF 1 (2 ^ 47 - 1 - Z.of_nat m) 0); (29%nat, mkAF lo hi 0); (32%nat, mkAF llo lhi 0)] [] [].
Definition wb10a_ss (m : nat) (t4v : sv) (lo hi llo lhi : Z) : sstate :=
  mkSS WB10_T (wb10a_sr t4v) (wb10a_mem m) None (wb10a_G m lo hi llo lhi).
(* byte i of what is left, 0 past its end *)
Definition wb10a_b (r : list byte) (i : nat) : Z := nth i (rsb_u8s r) 0.
Definition wb10a_extra (len : Z) (r : list byte) : list word :=
  [w64 len; w64 (wb10a_b r 0); w64 (wb10a_b r 1); w64 (wb10a_b r 2); w64 (wb10a_b r 3)].
(* the registers the piece writes (a0 .. a7, s6), and the pinned one *)
Definition wb10a_clob : list (bv 5) :=
  [Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 14; Z_to_bv 5 15; Z_to_bv 5 16;
   Z_to_bv 5 17; Z_to_bv 5 22].
Definition wb10a_pins (t4v : sv) : list (bv 5 * sv) := [(Z_to_bv 5 29, t4v)].

(* ======================================== 2. the model ======================================== *)
Lemma wb10a_b_eq : forall r i, wb10a_b r i = bv_unsigned (nth i r (Z_to_bv 8 0)).
Proof.
intros r. unfold wb10a_b, rsb_u8s. induction r as [|b r IH]; intros [|i]; cbn [map nth]; try reflexivity. apply IH.
Qed.
Lemma wb10a_b_range : forall r i, 0 <= wb10a_b r i < 256.
Proof. intros r i. rewrite wb10a_b_eq. apply Cursor.byte_range. Qed.
Lemma wb10a_b_skipn : forall (l : list byte) j i, wb10a_b (skipn j l) i = nth (j + i) (rsb_u8s l) 0.
Proof.
intros l j i. unfold wb10a_b, rsb_u8s. revert l. induction j as [|j IH]; intros l; [reflexivity|].
destruct l as [|b l]; cbn [skipn map].
- destruct i; reflexivity.
- cbn [Nat.add nth]. apply IH.
Qed.

Lemma wb10a_off_bound : forall plen x, 8 < plen -> 8 <= 8 + x mod (plen - 8) < plen.
Proof. intros plen x H. pose proof (Z.mod_pos_bound x (plen - 8) ltac:(lia)). lia. Qed.

(* one, two or three bytes from c on (no count byte): an offset, nothing written *)
Lemma wb10a_m_rt_short : forall plen (c : byte) r1, bv_unsigned c mod 16 = 15 -> 8 < plen -> (length r1 <= 2)%nat ->
  fst (corr_step plen (c :: r1)) = Some (8 + fst (fuzz_u16 r1) mod (plen - 8), []).
Proof.
intros plen c r1 Hc Hl Hr. rewrite (wb10_corr_some plen c r1 Hc Hl), (wb10_corr_empty_tail r1 Hr).
pose proof (wb10a_off_bound plen (fst (fuzz_u16 r1)) Hl) as Hb.
rewrite Z.mod_0_l by lia. rewrite Z.min_l by lia. reflexivity.
Qed.
(* a count byte n with n mod 8 = 0: an offset, nothing written *)
Lemma wb10a_m_rt_n0 : forall plen (c b1 b2 nb : byte) r4, bv_unsigned c mod 16 = 15 -> 8 < plen ->
  bv_unsigned nb mod 8 = 0 ->
  fst (corr_step plen (c :: b1 :: b2 :: nb :: r4)) =
  Some (8 + (bv_unsigned b1 + 256 * bv_unsigned b2) mod (plen - 8), []).
Proof.
intros plen c b1 b2 nb r4 Hc Hl Hn. rewrite (wb10_corr_some plen c (b1 :: b2 :: nb :: r4) Hc Hl).
cbn [fuzz_u16 fuzz_u8 skipn fst]. rewrite Hn.
pose proof (wb10a_off_bound plen (bv_unsigned b1 + 256 * bv_unsigned b2) Hl) as Hb.
rewrite Z.min_l by lia. reflexivity.
Qed.
(* the loop's arm: min(n mod 8, len - off) bytes from what follows n *)
Lemma wb10a_m_r : forall plen (c b1 b2 nb : byte) r4, bv_unsigned c mod 16 = 15 -> 8 < plen ->
  fst (corr_step plen (c :: b1 :: b2 :: nb :: r4)) =
  Some (8 + (bv_unsigned b1 + 256 * bv_unsigned b2) mod (plen - 8),
        fst (fuzz_u8s (Z.to_nat (Z.min (bv_unsigned nb mod 8)
                                       (plen - (8 + (bv_unsigned b1 + 256 * bv_unsigned b2) mod (plen - 8))))) r4)).
Proof.
intros plen c b1 b2 nb r4 Hc Hl. rewrite (wb10_corr_some plen c (b1 :: b2 :: nb :: r4) Hc Hl).
cbn [fuzz_u16 fuzz_u8 skipn fst]. reflexivity.
Qed.

(* ---- the values the engine computes ---- *)
Lemma wb10a_land15 : forall v, Z.land v 15 = v mod 16.
Proof. intros v. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wb10a_land7 : forall v, Z.land v 7 = v mod 8.
Proof. intros v. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Section u. Context {fx : YK11.FPState}.
Lemma wb10a_U_and15 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SExt false 8 (SOff n 0)) (SLit 15)) = v mod 16.
Proof.
intros E n v Hn Hv. rewrite U_SAlu, U_SLit, (U_zext8 E n v Hn Hv). cbn [zalu_raw].
rewrite (zcanon_id 15) by (unfold M64; lia). rewrite wb10a_land15.
pose proof (Z.mod_pos_bound v 16 ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
Lemma wb10a_U_and7 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SExt false 8 (SOff n 0)) (SLit 7)) = v mod 8.
Proof.
intros E n v Hn Hv. rewrite U_SAlu, U_SLit, (U_zext8 E n v Hn Hv). cbn [zalu_raw].
rewrite (zcanon_id 7) by (unfold M64; lia). rewrite wb10a_land7.
pose proof (Z.mod_pos_bound v 8 ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
Lemma wb10a_br_c : forall E b c,
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SExt false 8 (SOff 33 0)) (SLit 15))) (sv_denot E (SLit 15)) = b ->
  ew E 33 = Z_to_bv 64 c -> 0 <= c < 256 -> negb (c mod 16 =? 15) = b.
Proof.
intros E b c Hb H33 Hc. rewrite YI04.branch_ne_U in Hb.
rewrite (wb10a_U_and15 E 33 c H33 Hc), U_SLit in Hb.
rewrite (zcanon_id 15) in Hb by (unfold M64; lia). exact Hb.
Qed.
Lemma wb10a_br_n : forall E b n,
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SExt false 8 (SOff 36 0)) (SLit 7))) (sv_denot E (SLit 0)) = b ->
  ew E 36 = Z_to_bv 64 n -> 0 <= n < 256 -> (n mod 8 =? 0) = b.
Proof.
intros E b n Hb H36 Hn. rewrite YI04.branch_eq_U in Hb.
rewrite (wb10a_U_and7 E 36 n H36 Hn), U_SLit in Hb.
rewrite (zcanon_id 0) in Hb by (unfold M64; lia). exact Hb.
Qed.
(* a4 at R: (b2 << 8 | b1) remu (len - 8) + 8 *)
Lemma wb10a_den_off : forall E b1 b2 len, ew E 34 = Z_to_bv 64 b1 -> ew E 35 = Z_to_bv 64 b2 ->
  ew E 32 = Z_to_bv 64 len -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 9 <= len <= 5440 ->
  sv_denot E (SAlu ALU_ADD (SMd M_REMU (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 35 0)) (SLit 8))
                                          (SExt false 8 (SOff 34 0))) (SOff 32 (-8))) (SLit 8))
  = Z_to_bv 64 (8 + (b1 + 256 * b2) mod (len - 8)).
Proof.
intros E b1 b2 len H34 H35 H32 Hb1 Hb2 Hl. rewrite denot_lit_U. f_equal.
assert (V1 : U E (SExt false 8 (SOff 34 0)) = b1) by (apply U_zext8; assumption).
assert (V2 : U E (SExt false 8 (SOff 35 0)) = b2) by (apply U_zext8; assumption).
assert (VO : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 35 0)) (SLit 8)) (SExt false 8 (SOff 34 0)))
  = b1 + b2 * 2 ^ 8).
{ apply (U_or_sll E _ _ _ _ 8 V2 V1); change (2 ^ 8) with 256; first [lia | (vm_compute; reflexivity)]. }
assert (VL : U E (SOff 32 (-8)) = len - 8) by (apply (U_atom_off E 32 len (-8) H32); lia).
rewrite U_SAlu, U_SMd, VO, VL, U_SLit. cbn [zalu_raw zmd_raw].
rewrite (proj2 (Z.eqb_neq (len - 8) 0)) by lia. change (2 ^ 8) with 256.
pose proof (Z.mod_pos_bound (b1 + b2 * 256) (len - 8) ltac:(lia)) as Hm.
rewrite (zcanon_id 8) by (unfold M64; lia). rewrite (zcanon_id ((b1 + b2 * 256) mod (len - 8))) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia).
replace (b1 + b2 * 256) with (b1 + 256 * b2) by ring. lia.
Qed.
End u.

(* ======================================== 3. the cut T and the run's end ======================================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma wb10a_aview_all : forall H (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs H m' a = aview rsegs H m a) -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros H m m' K a.
assert (Hm : forall mm, aview rsegs H mm a = aview rsegs H mm (a mod 2 ^ 64))
  by (intros mm; unfold aview, mbyte; rewrite Z_to_bv_mod64; reflexivity).
rewrite (Hm m'), (Hm m). apply K. apply Z.mod_pos_bound. lia.
Qed.

(* a run with no write window keeps every byte *)
Lemma wb10a_kept_run : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs H m1 a = aview rsegs H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> (forall a, ~ in_wrange E rs a) ->
  forall a, 0 <= a < 2 ^ 64 -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros E rs H m0 m1 m2 HK HF HW a Ha. rewrite <- (HK a Ha). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. apply HW.
Qed.

(* the input's bytes against the cells the piece reads *)
Lemma wb10a_in_apart : forall (cx : rsb_scx rsegs) rest, rsb_in rsegs cx rest -> forall a,
  q_src (x_e cx) <= a < q_src (x_e cx) + q_left (x_e cx) ->
  ~ (q_R (x_e cx) + 0x150 <= a < q_R (x_e cx) + 0x180) /\ ~ (q_pp (x_e cx) <= a < q_pp (x_e cx) + PP_SIZE).
Proof.
intros cx rest Hin a Ha. destruct Hin as (_ & _ & _ & _ & _ & _ & _ & Hapart).
destruct (Hapart a Ha) as (_ & N2 & N3). split; [|exact N3].
intros X. apply N2. unfold rt_inw. cbn [hi_w1 rate_himg_B].
do 4 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
Qed.

(* len, pp->len and the record's length *)
Lemma wb10a_len : forall (cx : rsb_scx rsegs) rest sh ps r (W2 : world rsegs) mem2,
  rsb_pp_at rsegs cx W2 mem2 (pp_bytes (PodRec sh ps None)) -> rsb_wf sh ps -> q_len (x_e cx) = rt_len rest ->
  fst (pod_build rest) = PodRec sh ps (fst (corr_step (rsb_plen sh ps) r)) ->
  q_len (x_e cx) = rsb_plen sh ps /\ 8 <= rsb_plen sh ps <= 5440 /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 (rsb_plen sh ps).
Proof.
intros cx rest sh ps r W2 mem2 Hpp Hwf Hlen Htie.
destruct (wb10_wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2 & _).
assert (Hq : q_len (x_e cx) = rsb_plen sh ps).
{ rewrite Hlen. unfold rt_len, rsb_plen. rewrite Htie.
  destruct (wb10_rec_facts rest) as (Hrw & _). rewrite Htie in Hrw.
  destruct Hrw as (_ & _ & _ & _ & _ & Hc). cbn [p_corr] in Hc.
  rewrite (wb10_buf_len sh ps _ Hc). rewrite HL2. reflexivity. }
split; [exact Hq|]. split; [unfold rsb_plen; lia|].
assert (Hb : Z.of_nat (length (buf (PodRec sh ps None))) <= POD_BUF_MAX)
  by (cbn [buf p_corr]; rewrite HL2; unfold POD_BUF_MAX; lia).
pose proof (rtmb_pp_len rsegs (buf (PodRec sh ps None)) _ _ _ _ _ Hb HE1 HE2 (w_H W2) mem2 (q_pp (x_e cx)) Hpp) as V.
cbn [buf p_corr] in V. rewrite HL2 in V. exact V.
Qed.

(* the numbers and facts of the cut T the runs use *)
Lemma wb10a_ctx : forall cx rest sh ps r ly2 S2 W2 regs2 mem2 md2,
  rsb_start_M01 rsegs B cx rest -> wb10_cut_T B MT cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 (Z_to_bv 5 20) = w64 SHADOW_OFF /\ getr regs2 (Z_to_bv 5 7) = w64 (q_pp (x_e cx) + 0x4000) /\
  getr regs2 (Z_to_bv 5 29) = w64 (Z.of_nat (length r)) /\
  getr regs2 (Z_to_bv 5 26) = w64 (rsb_cur rsegs cx rest r) /\
  In (q_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2) /\
  4096 <= q_pp (x_e cx) /\ q_pp (x_e cx) + 19744 <= alloc_ceiling /\
  q_len (x_e cx) = rsb_plen sh ps /\ 8 <= rsb_plen sh ps <= 5440 /\
  1 <= rsb_cur rsegs cx rest r /\ rsb_cur rsegs cx rest r + Z.of_nat (length r) <= 2 ^ 47 - 1 /\
  Z.of_nat (length r) <= 2 ^ 63 /\
  (forall i, 0 <= i < Z.of_nat (length r) ->
     range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (rsb_cur rsegs cx rest r + i) 1).
Proof.
intros cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 Hst Hcut.
destruct Hst as (HP & Hfsh0 & _).
destruct Hcut as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie).
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinb & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (wb10a_len cx rest sh ps r W2 mem2 Hpp Hwf Hlen Htie) as (Hq & HLb & _).
unfold rsb_at_cx, rsb_at, rsb_L_post, rsb_Hc in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P20 & P7 & P24 & Q8 & Q10 & Q50 & Q60 & Qf8 & Q120 & Q138 & Q168 & Q170
  & Q48 & Q30 & Q38 & Q40 & Q18 & Q148 & Q108 & P29 & P26 & _).
cbn [fst snd rt_at] in P20, P7, P29, P26.
pose proof Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
destruct Hsuf as (j & Hj & Er).
assert (Lr : length r = (length rest - j)%nat) by (rewrite Er; apply length_skipn).
assert (Hcur : rsb_cur rsegs cx rest r = q_src (x_e cx) + Z.of_nat j) by (unfold rsb_cur; rewrite Lr; lia).
assert (Hend : q_src (x_e cx) + q_left (x_e cx) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
split; [exact P20|]. split; [exact P7|]. split; [exact P29|]. split; [exact P26|]. split; [exact Hinb|].
split; [lia|]. split; [lia|]. split; [exact Hq|]. split; [exact HLb|].
split; [rewrite Hcur; lia|]. split; [rewrite Hcur; lia|]. split; [lia|].
intros i Hi. rewrite Hcur.
destruct (wb10_input_now B MT cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat j + i) HP Hin Hfsh0 HC Hfsh ltac:(lia))
  as (_ & RA). rewrite Z.add_assoc in RA. exact RA.
Qed.

(* the entry state of a run from T: m input bytes in a region, t4 as t4v with |r| in [lo, hi], len in [llo, lhi] *)
Lemma wb10a_rin_ok : forall E (W : world rsegs) mem cur (m : nat) (r : list byte),
  ew E 26 = Z_to_bv 64 cur -> (forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (wb10a_b r i)) ->
  (m <= 4)%nat -> 0 <= cur -> cur + 4 <= 2 ^ 64 ->
  (forall i, (i < m)%nat -> val_mem rsegs (mrestrict (w_H W) mem) (cur + Z.of_nat i) 1 (wb10a_b r i)) ->
  region_ok rsegs E (mrestrict (w_H W) mem) (wb10a_rin m).
Proof.
intros E W mem cur m r E26 Eb Hm Hc0 Hc1 Hv. unfold region_ok, wb10a_rin.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E26, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold wb10a_bchunks. apply Forall_forall. intros ch Hin. apply in_map_iff in Hin as (i & <- & Hi).
apply in_seq in Hi.
apply (chunk_ok_val rsegs E (mrestrict (w_H W) mem) cur (Z.of_nat i) 1 (SOff (33 + i) 0) (wb10a_b r i)).
- cbn [sv_denot]. rewrite (Eb i ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 1)) with 256. apply wb10a_b_range.
- lia.
- apply Hv. lia.
Qed.

Lemma wb10a_entry : forall cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 (m : nat) (t4v : sv) lo hi llo lhi,
  rsb_start_M01 rsegs B cx rest -> wb10_cut_T B MT cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  (m <= length r)%nat -> (m <= 4)%nat ->
  getr regs2 (Z_to_bv 5 29) = sv_denot (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) t4v ->
  lo <= Z.of_nat (length r) <= hi -> 0 <= lo -> llo <= rsb_plen sh ps <= lhi -> 0 <= llo ->
  st_ok rsegs (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) (wb10a_ss m t4v lo hi llo lhi)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 WB10_T) mem2 (seg_rom rsegs))).
Proof.
intros cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 m t4v lo hi llo lhi Hst Hcut Hm Hm4 H29 Hlo Hlo0 Hll Hll0.
pose proof Hst as (HP & Hfsh0 & _).
pose proof Hcut as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie).
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinb & Hfresh & Hal & Hlo4 & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (wb10_R_bounds B cx HP) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7 & RB8).
pose proof (wb10a_ctx cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 Hst Hcut)
  as (_ & _ & _ & _ & _ & _ & _ & Hq & HLb & Hc1 & Hc2 & Hr63 & _).
destruct (wb10a_len cx rest sh ps r W2 mem2 Hpp Hwf Hlen Htie) as (_ & _ & HLv).
unfold rsb_at_cx, rsb_at, rsb_L_post, rsb_Hc in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P20 & P7 & P24 & Q8 & Q10 & Q50 & Q60 & Qf8 & Q120 & Q138 & Q168 & Q170
  & Q48 & Q30 & Q38 & Q40 & Q18 & Q148 & Q108 & P29 & P26 & _).
cbn [fst snd rt_at rt_xv] in P9, P20, P7, P29, P26, Q170.
pose proof Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
pose proof Hsuf as (j & Hj & Er).
assert (Lr : length r = (length rest - j)%nat) by (rewrite Er; apply length_skipn).
set (cur := rsb_cur rsegs cx rest r) in *.
assert (Hcur : cur = q_src (x_e cx) + Z.of_nat j) by (unfold cur, rsb_cur; rewrite Lr; lia).
assert (Hsa : 0 <= shadow_addr (q_pp (x_e cx) + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  assert (0 <= (q_pp (x_e cx) + 0x4000) / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
rewrite Z.mod_small in Q170 by exact Hsa.
set (len := rsb_plen sh ps) in *.
set (E := Ereg regs2 (wb10a_extra len r)).
assert (E9 : bv_unsigned (ew E 9) = q_R (x_e cx)).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), P9. unfold w64. apply unsigned_lit_small. lia. }
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact P20).
assert (E7 : ew E 7 = Z_to_bv 64 (q_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact P7).
assert (E26 : ew E 26 = Z_to_bv 64 cur)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 (Z_to_bv 5 26) eq_refl); exact P26).
assert (E29 : ew E 29 = Z_to_bv 64 (Z.of_nat (length r)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 29 (Z_to_bv 5 29) eq_refl); exact P29).
assert (E32 : ew E 32 = Z_to_bv 64 len) by reflexivity.
assert (Eb : forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (wb10a_b r i)).
{ intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia); reflexivity. }
(* the input bytes: the first m of r *)
assert (Hbytes : forall i, (i < m)%nat -> val_mem rsegs (mrestrict (w_H W2) mem2) (cur + Z.of_nat i) 1 (wb10a_b r i)).
{ intros i Hi.
  destruct (wb10_input_now B MT cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat (j + i)) HP Hin Hfsh0 HC Hfsh ltac:(lia))
    as (V & _).
  rewrite Nat2Z.id in V. rewrite Er, wb10a_b_skipn.
  replace (cur + Z.of_nat i) with (q_src (x_e cx) + Z.of_nat (j + i)) by lia. exact V. }
(* apartness of the three regions *)
assert (Hap : forall i, (i < m)%nat ->
  ~ (q_R (x_e cx) + 0x150 <= cur + Z.of_nat i < q_R (x_e cx) + 0x180) /\
  ~ (q_pp (x_e cx) <= cur + Z.of_nat i < q_pp (x_e cx) + PP_SIZE)).
{ intros i Hi. apply (wb10a_in_apart cx rest Hin). lia. }
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- unfold wb10a_sr. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact H29].
- destruct m as [|[|[|[|[|m]]]]]; try (exfalso; lia); vm_compute; reflexivity.
- fold E. unfold wb10a_mem.
  assert (R0 : region_ok rsegs E (mrestrict (w_H W2) mem2) wb10a_rsh).
  { apply (rtmb_ro_region rsegs E (w_H W2) mem2 9 (q_R (x_e cx))); [exact E9 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ (q_R (x_e cx)) 0x170 8 wb10a_sh (shadow_addr (q_pp (x_e cx) + 0x4000)));
      [ unfold wb10a_sh; exact (wb10_den_sh E 7 20 (q_pp (x_e cx) + 0x4000) E7 ltac:(lia) E20)
      | cbn; lia | cbn; lia | exact Q170]. }
  assert (R1 : region_ok rsegs E (mrestrict (w_H W2) mem2) wb10a_rlen).
  { apply (rtmb_ro_region rsegs E (w_H W2) mem2 7 (q_pp (x_e cx) + 0x4000));
      [rewrite E7; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ (q_pp (x_e cx) + 0x4000) 0 8 (SOff 32 0) len);
      [exact (wb10_den_atom E 32 len E32) | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HLv]. }
  destruct m as [|m'].
  + constructor; [exact R0|]. constructor; [exact R1 | constructor].
  + constructor; [exact R0|]. constructor; [exact R1|]. constructor; [|constructor].
    apply (wb10a_rin_ok E W2 mem2 cur (S m') r E26 Eb Hm4 ltac:(lia) ltac:(lia) Hbytes).
- fold E. unfold wb10a_mem.
  assert (Hpr : q_pp (x_e cx) + 0x4008 <= q_R (x_e cx)) by (unfold T_SEG_STK, ASTACK in *; lia).
  destruct m as [|m'].
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, wb10a_rsh, wb10a_rlen.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E7, unsigned_lit_small by lia. repeat split; lia.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, wb10a_rsh, wb10a_rlen, wb10a_rin.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E7, E26, !unsigned_lit_small by lia.
    destruct (Hap 0%nat ltac:(lia)) as (A0 & B0). destruct (Hap m' ltac:(lia)) as (A1 & B1).
    unfold PP_SIZE in *. repeat split; lia.
- fold E. unfold facts_ok, wb10a_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2].
  rewrite E7, E20, E26, E29, E32, !unsigned_lit_small by (unfold SHADOW_OFF, WB10_HI; lia).
  repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, WB10_HI; lia);
  try (rewrite Z.pow_0_r; apply Z.mod_1_r).
  change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
Qed.

(* ---- the cut's facts after a run that wrote nothing and kept every register outside wb10a_clob ---- *)
Lemma wb10a_keep : forall cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  wb10_cut_T B MT cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr wb10a_clob -> getr regs3 rr = getr regs2 rr) ->
  rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 /\
  rsb_at_cx rsegs cx W2 mem3 regs3 (rsb_L_post rsegs cx) /\
  rsb_at_cx rsegs cx W2 mem3 regs3 [(LCell XR 0x108, Z.lnot (q_pp (x_e cx)))] /\
  rsb_fsh_at rsegs cx W2 mem3 rsb_P0 /\
  rsb_pp_at rsegs cx W2 mem3 (pp_bytes (PodRec sh ps None)).
Proof.
intros cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcut HJ3 Hio HK RK.
destruct Hcut as (HC & HL & Hfsh & Hpp & _).
pose proof (wb10a_aview_all _ _ _ HK) as HKa.
unfold rsb_at_cx, rsb_at in HL. apply Forall_app in HL as [HL HT].
split; [|split; [|split; [|split]]].
- apply (wb10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (fun _ => False) HC HJ3).
  + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply wb10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + exact Hio.
  + intros a Ha _. exact (HK a Ha).
  + intros a [].
- unfold rsb_at_cx, rsb_at.
  apply (rtmb_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ HL).
  intros f Hf. unfold rsb_L_post, rsb_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rtmb_keeps rt_xv];
    first [ (apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply HKa) ] |]).
  destruct Hf.
- unfold rsb_at_cx, rsb_at. apply Forall_cons_iff in HT as [H108 _].
  apply (rtmb_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx)).
  + constructor; [exact H108 | constructor].
  + intros f [<-|[]]. cbn [fst rtmb_keeps rt_xv]. intros i Hi. apply HKa.
- apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (q_F (x_e cx)) rsb_P0 Hfsh). intros i Hi. apply HKa.
- apply (rtmb_bytes_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (q_pp (x_e cx)) _ Hpp). intros x Hx. apply HKa.
Qed.

(* ---- the four ends ---- *)
Lemma wb10a_end_tail : forall cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  rsb_start_M01 rsegs B cx rest -> rsb_from_C2 rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr wb10a_clob -> getr regs3 rr = getr regs2 rr) ->
  fst (corr_step (rsb_plen sh ps) r) = None ->
  SRr rsegs W2 (cfg_at rsegs 0x82a14 regs3 mem3 md3) POST.
Proof.
intros cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hst HC2 Hcut HJ3 Hio HK RK Hno.
destruct (wb10a_keep cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcut HJ3 Hio HK RK)
  as (HC3 & HL3 & _ & Hfsh3 & Hpp3).
pose proof Hcut as (_ & _ & _ & _ & _ & _ & _ & Hlen & Htie).
apply (wb10_tail B MT cx POST rest ly2 S2 W2 regs3 mem3 md3 (proj1 Hst) HC2 HC3 HL3 Hfsh3); [|exact Hlen].
rewrite Htie, Hno. exact Hpp3.
Qed.

Lemma wb10a_end_tail8 : forall cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  rsb_start_M01 rsegs B cx rest -> rsb_from_C2 rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr wb10a_clob -> getr regs3 rr = getr regs2 rr) ->
  getr regs3 (Z_to_bv 5 22) = w64 (q_len (x_e cx)) ->
  fst (corr_step (rsb_plen sh ps) r) = None ->
  SRr rsegs W2 (cfg_at rsegs 0x82a24 regs3 mem3 md3) POST.
Proof.
intros cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hst HC2 Hcut HJ3 Hio HK RK R22 Hno.
destruct (wb10a_keep cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcut HJ3 Hio HK RK)
  as (HC3 & HL3 & _ & Hfsh3 & Hpp3).
pose proof Hcut as (_ & _ & _ & _ & _ & _ & _ & Hlen & Htie).
apply (wb10_tail8 B MT cx POST rest ly2 S2 W2 regs3 mem3 md3 (proj1 Hst) HC2 HC3 HL3 R22 Hfsh3); [|exact Hlen].
rewrite Htie, Hno. exact Hpp3.
Qed.

Lemma wb10a_end_RT : forall cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off,
  rsb_from_RT rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr wb10a_clob -> getr regs3 rr = getr regs2 rr) ->
  fst (corr_step (rsb_plen sh ps) r) = Some (off, []) -> 8 <= off -> off <= rsb_plen sh ps ->
  SRr rsegs W2 (cfg_at rsegs RSB_RT regs3 mem3 md3) POST.
Proof.
intros cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off HRT Hcut HJ3 Hio HK RK Hso Ho1 Ho2.
destruct (wb10a_keep cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcut HJ3 Hio HK RK)
  as (HC3 & HL3 & _ & Hfsh3 & Hpp3).
pose proof Hcut as (_ & _ & _ & _ & Hin & Hsuf & Hwf & Hlen & Htie).
apply (HRT ly2 S2 W2 regs3 mem3 md3 sh ps off [] r).
split; [exact HC3|]. split; [exact HL3|]. split; [exact Hfsh3|].
split; [unfold rsb_img_corr; cbn [length Z.of_nat Z.to_nat firstn]; rewrite wb10_overwrite_nil;
        rewrite <- wb10_bytes_none; exact Hpp3|].
split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen|].
split; [rewrite Htie, Hso; reflexivity|]. cbn [length Z.of_nat]. split; [exact Ho1|]. split; [lia | lia].
Qed.

Lemma wb10a_end_R : forall cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off bs cnt r',
  rsb_from_R rsegs B MT cx POST rest 0 ->
  wb10_cut_T B MT cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr wb10a_clob -> getr regs3 rr = getr regs2 rr) ->
  fst (corr_step (rsb_plen sh ps) r) = Some (off, bs) -> rsb_corr_wf sh ps off bs cnt -> rsb_suffix rest r' ->
  bs = fst (fuzz_u8s (length bs) r') ->
  getr regs3 (Z_to_bv 5 13) = w64 0 -> getr regs3 (Z_to_bv 5 12) = w64 cnt -> getr regs3 (Z_to_bv 5 14) = w64 off ->
  getr regs3 (Z_to_bv 5 10) = w64 (rsb_cur rsegs cx rest r') ->
  getr regs3 (Z_to_bv 5 15) = w64 (Z.of_nat (length r')) -> getr regs3 (Z_to_bv 5 16) = w64 1 ->
  SRr rsegs W2 (cfg_at rsegs RSB_R regs3 mem3 md3) POST.
Proof.
intros cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off bs cnt r' HR Hcut HJ3 Hio HK RK
  Hso Hwfc Hsuf' Hbs R13 R12 R14 R10 R15 R16.
destruct (wb10a_keep cx sh ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcut HJ3 Hio HK RK)
  as (HC3 & HL3 & H108 & Hfsh3 & Hpp3).
pose proof Hcut as (_ & _ & _ & _ & Hin & Hsuf & Hwf & Hlen & Htie).
pose proof Hwfc as (W1 & W2' & W3 & W4 & W5).
apply (HR ly2 S2 W2 regs3 mem3 md3 sh ps r' off bs cnt). change (Z.of_nat 0) with 0.
split; [exact HC3|]. split.
{ unfold rsb_at_cx. apply wb10_at_app; [exact HL3|].
  unfold rsb_at_cx, rsb_at in H108. apply Forall_cons_iff in H108 as [H108 _]. cbn [fst snd rt_at] in H108.
  unfold rsb_at. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rt_at]; try assumption.
  rewrite Z.sub_0_r. exact R12. }
split; [exact Hfsh3|].
split; [unfold rsb_img_corr; cbn [Z.to_nat firstn]; rewrite wb10_overwrite_nil;
        rewrite <- wb10_bytes_none; exact Hpp3|].
split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|]. split; [exact Hlen|].
split; [rewrite Htie, Hso; reflexivity|]. split; [exact Hwfc|]. split; [lia|]. split; [lia|].
cbn [Z.to_nat skipn]. rewrite Nat.sub_0_r. exact Hbs.
Qed.

(* the pinned register holds its entry value *)
Lemma wb10a_pins_ok : forall E Ef (regs : bvmap 5 word) t4v,
  (forall rr, getr regs rr = sv_denot E (sr_get (wb10a_sr t4v) rr)) -> env_agree 32 E Ef ->
  sv_atoms_lt 32 t4v = true ->
  forall rr e, In (rr, e) (wb10a_pins t4v) -> sv_denot Ef e = getr regs rr.
Proof.
intros E Ef regs t4v HR0 HA Hs rr e Hin. cbn [wb10a_pins In] in Hin.
destruct Hin as [Heq|[]]; injection Heq as <- <-.
rewrite (sv_denot_agree 32 E Ef t4v HA Hs). rewrite HR0. reflexivity.
Qed.

(* the obligation of an input read: its byte is addressable, as at T *)
Lemma wb10a_ob_in : forall E (H : word -> bool) (m0 m : word -> option byte) cur i,
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs H m a = aview rsegs H m0 a) ->
  ew E 20 = Z_to_bv 64 SHADOW_OFF -> ew E 26 = Z_to_bv 64 cur -> 0 <= cur -> 0 <= i -> cur + i < 2 ^ 47 ->
  range_addressable (aview rsegs H m0) SHADOW_OFF (cur + i) 1 ->
  range_addressable (rd_of rsegs (mrestrict H m)) (U E WB10Bx) (U E (SOff 26 i)) 1.
Proof.
intros E H m0 m cur i KE E20 E26 Hc0 Hi0 Hc1 RA. unfold WB10Bx.
rewrite (U_atom E 20 SHADOW_OFF E20 ltac:(unfold SHADOW_OFF; lia)), (U_atom_off E 26 cur i E26 ltac:(lia) ltac:(lia)).
rewrite <- (aview_rd_of rsegs). apply (rtmb_ra_kept rsegs H m0 H m SHADOW_OFF (cur + i) 1 RA).
intros x Hx. apply KE. unfold shadow_of_addr, SHADOW_OFF.
assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.
End a.

(* ======================================== 4. the runs ======================================== *)
(* an env slot below the run's tokens *)
Ltac wb10a_ew H := rewrite ?ew_ewset_other by lia; exact H.
(* every byte kept by a run without a write window *)
Ltac wb10a_kwr :=
  idtac; let a := fresh "a" in let rg := fresh "rg" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (rg & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
Ltac wb10a_keep_tac :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _),
                      KE : forall a, _ -> aview _ _ _ a = _ |- _ =>
    let KS := fresh "KS" in
    pose proof (wb10a_kept_run _ _ _ _ _ _ KE HFr ltac:(wb10a_kwr)) as KS; clear KE HFr; rename KS into KE end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac wb10a_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
                                      SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok wb10_tbl_ok HS HJ SHOK WB10Bspan end.
Ltac wb10a_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
                                      SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan pc end.
Ltac wb10a_branch Hc :=
  lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok wb10_tbl_ok HS SH WB10Bspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac wb10a_env_of Hc := lazymatch type of Hc with branch_taken _ (sv_denot ?Ek _) _ = _ => Ek end.
Ltac wb10a_kio := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
(* the shadow obligations a run leaves: the 8 bytes of pp->len (the first block) and the input byte at cursor + i *)
Ltac wb10a_ob HJ Hinb E20 E7 E26 KE Hra :=
  cbn [ms_mem mkst];
  lazymatch goal with
  | |- range_addressable _ _ (U _ (SOff 7 0)) 8 =>
      lazymatch type of Hinb with In (?p, ?sz) _ =>
        eapply (wb10_ob_blk _ _ _ _ _ _ _ p sz (p + 0x4000) 8 (SOff 7 0) (proj1 HJ) Hinb);
        [ lia | change (req_size PP_SIZE) with 19744; lia
        | unfold WB10Bx; apply wb10_U_atom; [wb10a_ew E20 | unfold SHADOW_OFF; lia]
        | apply wb10_U_atom; [wb10a_ew E7 | lia] ] end
  | |- range_addressable _ _ (U _ (SOff 26 ?i)) 1 =>
      lazymatch type of E26 with ew _ 26 = Z_to_bv 64 ?cur =>
        apply (wb10a_ob_in _ _ _ _ cur i KE); [wb10a_ew E20 | wb10a_ew E26 | lia | lia | lia | apply Hra; lia] end
  end.
(* the registers a run kept, and the goal's state in the cfg_at form *)
Ltac wb10a_fin regs2 W2 extra t4v E HAE HR0 :=
  lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
    pose proof (regs_kept_of_st_ok_pins rsegs Ef ssf msf regs2 extra (w_H W2)
      wb10a_clob (wb10a_pins t4v) HSf ltac:(env_agree_chain HAE)
      (wb10a_pins_ok E Ef regs2 t4v HR0 ltac:(env_agree_chain (env_agree_refl 32 E)) eq_refl)
      ltac:(vm_compute; reflexivity)) as RK;
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ msf HSf eq_refl); cbn [ss_pc]
  end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- len >= 9, |r| >= 4 ---- *)
Lemma wb10a_c4 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps (c b1 b2 nb : byte) r4,
  rsb_start_M01 rsegs B cx rest -> rsb_from_R rsegs B MT cx POST rest 0 -> rsb_from_RT rsegs B MT cx POST rest ->
  rsb_from_C2 rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest (c :: b1 :: b2 :: nb :: r4) ly2 S2 W2 regs2 mem2 md2 -> 9 <= rsb_plen sh ps ->
  SRr rsegs W2 (cfg_at rsegs WB10_T regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c b1 b2 nb r4 Hst HR HRT HC2 Hcut H9.
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
set (r := c :: b1 :: b2 :: nb :: r4) in *.
destruct (wb10a_ctx B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 Hst Hcut)
  as (H20 & H7 & H29 & H26 & Hinb & Hpp4 & Hppc & Hq & HLb & Hc1 & Hc2 & Hr63 & Hra).
pose proof Hcut as (HC & _ & _ & _ & _ & Hsuf & _).
pose proof HC as (HJ & _).
pose proof asan_consts as (C1 & _).
assert (Lr : length r = S (S (S (S (length r4))))) by reflexivity.
set (cur := rsb_cur rsegs cx rest r) in *.
remember (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) as E eqn:HE.
assert (HS : st_ok rsegs E (wb10a_ss 4 (SOff 29 0) 4 (2 ^ 63) 9 5440)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 WB10_T) mem2 (seg_rom rsegs)))).
{ subst E. apply (wb10a_entry B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 4 (SOff 29 0) 4 (2 ^ 63) 9 5440 Hst Hcut);
    [rewrite Lr; lia | lia | | rewrite Lr; lia | lia | lia | lia].
  rewrite (wb10_den_atom _ 29 (Z.of_nat (length r))); [exact H29|].
  rewrite (ew_Ereg_nat regs2 _ 29 (Z_to_bv 5 29) eq_refl). exact H29. }
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E7 : ew E 7 = Z_to_bv 64 (q_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact H7).
assert (E26 : ew E 26 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 (Z_to_bv 5 26) eq_refl); exact H26).
assert (E29 : ew E 29 = Z_to_bv 64 (Z.of_nat (length r)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 29 (Z_to_bv 5 29) eq_refl); exact H29).
assert (E32 : ew E 32 = Z_to_bv 64 (rsb_plen sh ps)) by (subst E; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (bv_unsigned c)) by (subst E; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 (bv_unsigned b1)) by (subst E; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (bv_unsigned b2)) by (subst E; reflexivity).
assert (E36 : ew E 36 = Z_to_bv 64 (bv_unsigned nb)) by (subst E; reflexivity).
pose proof (Cursor.byte_range c) as Bc. pose proof (Cursor.byte_range b1) as Bb1.
pose proof (Cursor.byte_range b2) as Bb2. pose proof (Cursor.byte_range nb) as Bnb.
assert (HR0 : forall rr, getr regs2 rr = sv_denot E (sr_get (wb10a_sr (SOff 29 0)) rr))
  by (intros rr; exact (st_ok_restrict_reg rsegs (w_H W2) E _ _ rr HS)).
assert (HAE : env_agree 32 (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (Hra' : forall i, 0 <= i < 4 -> range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (cur + i) 1)
  by (intros i Hi; apply Hra; rewrite Lr; lia).
clear HE.
unfold cfg_at. change (w64 WB10_T) with (Z_to_bv 64 WB10_T).
(* 0x8270c .. 0x82738: the byte c *)
wb10a_run.
all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
wb10a_keep_tac.
wb10a_branch Hc.
- (* c mod 16 <> 15 -> 0x82a14 *)
  let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek true (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_true_iff, Z.eqb_neq in Hcc.
  wb10a_run_to 0x82a14. { awr_ok_tac. }
  wb10a_keep_tac.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SOff 29 0) E HAE HR0.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_tail B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _ Hst HC2 Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | apply wb10_corr_none; left; exact Hcc].
- let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek false (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_false_iff, Z.eqb_eq in Hcc.
  (* 0x8273c .. 0x82944: len (> 8), b1, b2, the trap 0x82918, n *)
  wb10a_run.
  all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
  wb10a_keep_tac.
  wb10a_branch Hn.
  + (* n mod 8 = 0 -> RT *)
    let Ek := wb10a_env_of Hn in
    pose proof (wb10a_br_n Ek true (bv_unsigned nb) Hn ltac:(wb10a_ew E36) Bnb) as Hnn.
    apply Z.eqb_eq in Hnn.
    wb10a_run_to RSB_RT. { awr_ok_tac. }
    wb10a_keep_tac.
    wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SOff 29 0) E HAE HR0.
    pose proof (wb10a_off_bound (rsb_plen sh ps) (bv_unsigned b1 + 256 * bv_unsigned b2) ltac:(lia)) as Hob.
    lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
      apply (wb10a_end_RT B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _
        (8 + (bv_unsigned b1 + 256 * bv_unsigned b2) mod (rsb_plen sh ps - 8)) HRT Hcut HJ)
    end; [wb10a_kio | exact KE | exact RK | apply wb10a_m_rt_n0; [exact Hcc | lia | exact Hnn] | lia | lia].
  + (* the loop's head R, turn 0 *)
    let Ek := wb10a_env_of Hn in
    pose proof (wb10a_br_n Ek false (bv_unsigned nb) Hn ltac:(wb10a_ew E36) Bnb) as Hnn.
    apply Z.eqb_neq in Hnn.
    wb10a_run_to RSB_R. { awr_ok_tac. }
    wb10a_keep_tac.
    pose proof (wb10a_off_bound (rsb_plen sh ps) (bv_unsigned b1 + 256 * bv_unsigned b2) ltac:(lia)) as Hob.
    set (off := 8 + (bv_unsigned b1 + 256 * bv_unsigned b2) mod (rsb_plen sh ps - 8)) in *.
    pose proof (Z.mod_pos_bound (bv_unsigned nb) 8 ltac:(lia)) as Hcnt.
    set (cnt := bv_unsigned nb mod 8) in *.
    set (k := Z.to_nat (Z.min cnt (rsb_plen sh ps - off))).
    assert (Hk : Z.of_nat k = Z.min cnt (rsb_plen sh ps - off)) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
    lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
      assert (R13 : getr (ms_regs msf) (Z_to_bv 5 13) = w64 0)
        by (rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ msf (Z_to_bv 5 13) HSf); wb10_sr_eval; reflexivity);
      assert (R12 : getr (ms_regs msf) (Z_to_bv 5 12) = w64 cnt)
        by (rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ msf (Z_to_bv 5 12) HSf); wb10_sr_eval;
            rewrite denot_lit_U; unfold w64; f_equal;
            exact (wb10a_U_and7 Ef 36 (bv_unsigned nb) ltac:(wb10a_ew E36) Bnb));
      assert (R14 : getr (ms_regs msf) (Z_to_bv 5 14) = w64 off)
        by (rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ msf (Z_to_bv 5 14) HSf); wb10_sr_eval;
            exact (wb10a_den_off Ef (bv_unsigned b1) (bv_unsigned b2) (rsb_plen sh ps)
              ltac:(wb10a_ew E34) ltac:(wb10a_ew E35) ltac:(wb10a_ew E32) Bb1 Bb2 ltac:(lia)));
      assert (R10 : getr (ms_regs msf) (Z_to_bv 5 10) = w64 (rsb_cur rsegs cx rest r4))
        by (rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ msf (Z_to_bv 5 10) HSf); wb10_sr_eval;
            rewrite (wb10_den_off Ef 26 cur 4 ltac:(wb10a_ew E26)); unfold w64; f_equal;
            unfold cur, rsb_cur; rewrite Lr; lia);
      assert (R15 : getr (ms_regs msf) (Z_to_bv 5 15) = w64 (Z.of_nat (length r4)))
        by (rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ msf (Z_to_bv 5 15) HSf); wb10_sr_eval;
            rewrite (wb10_den_off Ef 29 (Z.of_nat (length r)) (-4) ltac:(wb10a_ew E29)); unfold w64; f_equal;
            rewrite Lr; lia);
      assert (R16 : getr (ms_regs msf) (Z_to_bv 5 16) = w64 1)
        by (rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ msf (Z_to_bv 5 16) HSf); wb10_sr_eval; reflexivity)
    end.
    wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SOff 29 0) E HAE HR0.
    lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
      apply (wb10a_end_R B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _
        off (fst (fuzz_u8s k r4)) cnt r4 HR Hcut HJ)
    end;
    [wb10a_kio | exact KE | exact RK | apply wb10a_m_r; [exact Hcc | lia] | | | | exact R13 | exact R12 | exact R14
    | exact R10 | exact R15 | exact R16].
    * unfold rsb_corr_wf. rewrite wb10_length_fuzz_u8s, Hk. split; [lia|]. split; [lia|].
      split; [apply Nat2Z.inj_le; rewrite Hk; lia|]. split; lia.
    * replace r4 with (skipn 4 r) by reflexivity. apply wb10_suffix_skipn. exact Hsuf.
    * rewrite wb10_length_fuzz_u8s. reflexivity.
Qed.

(* ---- len >= 9, |r| = 3: b1 and b2 are read, no count byte ---- *)
Lemma wb10a_c3 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps (c b1 b2 : byte),
  rsb_start_M01 rsegs B cx rest -> rsb_from_RT rsegs B MT cx POST rest -> rsb_from_C2 rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest [c; b1; b2] ly2 S2 W2 regs2 mem2 md2 -> 9 <= rsb_plen sh ps ->
  SRr rsegs W2 (cfg_at rsegs WB10_T regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c b1 b2 Hst HRT HC2 Hcut H9.
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
set (r := [c; b1; b2]) in *.
destruct (wb10a_ctx B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 Hst Hcut)
  as (H20 & H7 & H29 & H26 & Hinb & Hpp4 & Hppc & Hq & HLb & Hc1 & Hc2 & Hr63 & Hra).
pose proof Hcut as (HC & _).
pose proof HC as (HJ & _).
pose proof asan_consts as (C1 & _).
assert (Lr : length r = 3%nat) by reflexivity.
set (cur := rsb_cur rsegs cx rest r) in *.
remember (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) as E eqn:HE.
assert (HS : st_ok rsegs E (wb10a_ss 3 (SLit 3) 3 3 9 5440)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 WB10_T) mem2 (seg_rom rsegs)))).
{ subst E. apply (wb10a_entry B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 3 (SLit 3) 3 3 9 5440 Hst Hcut);
    [rewrite Lr; lia | lia | exact H29 | rewrite Lr; lia | lia | lia | lia]. }
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E7 : ew E 7 = Z_to_bv 64 (q_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact H7).
assert (E26 : ew E 26 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 (Z_to_bv 5 26) eq_refl); exact H26).
assert (E33 : ew E 33 = Z_to_bv 64 (bv_unsigned c)) by (subst E; reflexivity).
pose proof (Cursor.byte_range c) as Bc.
assert (HR0 : forall rr, getr regs2 rr = sv_denot E (sr_get (wb10a_sr (SLit 3)) rr))
  by (intros rr; exact (st_ok_restrict_reg rsegs (w_H W2) E _ _ rr HS)).
assert (HAE : env_agree 32 (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (Hra' : forall i, 0 <= i < 3 -> range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (cur + i) 1)
  by (intros i Hi; apply Hra; rewrite Lr; lia).
clear HE.
unfold cfg_at. change (w64 WB10_T) with (Z_to_bv 64 WB10_T).
(* 0x8270c .. 0x82738: the byte c *)
wb10a_run.
all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
wb10a_keep_tac.
wb10a_branch Hc.
- (* c mod 16 <> 15 -> 0x82a14 *)
  let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek true (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_true_iff, Z.eqb_neq in Hcc.
  wb10a_run_to 0x82a14. { awr_ok_tac. }
  wb10a_keep_tac.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SLit 3) E HAE HR0.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_tail B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _ Hst HC2 Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | apply wb10_corr_none; left; exact Hcc].
- let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek false (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_false_iff, Z.eqb_eq in Hcc.
  (* 0x8273c .. 0x8291c: len (> 8), b1, b2, the trap 0x82918, then RT (a5 = t4 - 3 = 0) *)
  wb10a_run_to RSB_RT.
  all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
  wb10a_keep_tac.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SLit 3) E HAE HR0.
  pose proof (wb10a_off_bound (rsb_plen sh ps) (fst (fuzz_u16 [b1; b2])) ltac:(lia)) as Hob.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_RT B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _
      (8 + fst (fuzz_u16 [b1; b2]) mod (rsb_plen sh ps - 8)) HRT Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | apply wb10a_m_rt_short; [exact Hcc | lia | cbn; lia] | lia | lia].
Qed.

(* ---- len >= 9, |r| = 2: b1 is read, no count byte ---- *)
Lemma wb10a_c2 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps (c b1 : byte),
  rsb_start_M01 rsegs B cx rest -> rsb_from_RT rsegs B MT cx POST rest -> rsb_from_C2 rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest [c; b1] ly2 S2 W2 regs2 mem2 md2 -> 9 <= rsb_plen sh ps ->
  SRr rsegs W2 (cfg_at rsegs WB10_T regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c b1 Hst HRT HC2 Hcut H9.
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
set (r := [c; b1]) in *.
destruct (wb10a_ctx B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 Hst Hcut)
  as (H20 & H7 & H29 & H26 & Hinb & Hpp4 & Hppc & Hq & HLb & Hc1 & Hc2 & Hr63 & Hra).
pose proof Hcut as (HC & _).
pose proof HC as (HJ & _).
pose proof asan_consts as (C1 & _).
assert (Lr : length r = 2%nat) by reflexivity.
set (cur := rsb_cur rsegs cx rest r) in *.
remember (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) as E eqn:HE.
assert (HS : st_ok rsegs E (wb10a_ss 2 (SLit 2) 2 2 9 5440)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 WB10_T) mem2 (seg_rom rsegs)))).
{ subst E. apply (wb10a_entry B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 2 (SLit 2) 2 2 9 5440 Hst Hcut);
    [rewrite Lr; lia | lia | exact H29 | rewrite Lr; lia | lia | lia | lia]. }
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E7 : ew E 7 = Z_to_bv 64 (q_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact H7).
assert (E26 : ew E 26 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 (Z_to_bv 5 26) eq_refl); exact H26).
assert (E33 : ew E 33 = Z_to_bv 64 (bv_unsigned c)) by (subst E; reflexivity).
pose proof (Cursor.byte_range c) as Bc.
assert (HR0 : forall rr, getr regs2 rr = sv_denot E (sr_get (wb10a_sr (SLit 2)) rr))
  by (intros rr; exact (st_ok_restrict_reg rsegs (w_H W2) E _ _ rr HS)).
assert (HAE : env_agree 32 (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (Hra' : forall i, 0 <= i < 2 -> range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (cur + i) 1)
  by (intros i Hi; apply Hra; rewrite Lr; lia).
clear HE.
unfold cfg_at. change (w64 WB10_T) with (Z_to_bv 64 WB10_T).
(* 0x8270c .. 0x82738: the byte c *)
wb10a_run.
all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
wb10a_keep_tac.
wb10a_branch Hc.
- (* c mod 16 <> 15 -> 0x82a14 *)
  let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek true (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_true_iff, Z.eqb_neq in Hcc.
  wb10a_run_to 0x82a14. { awr_ok_tac. }
  wb10a_keep_tac.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SLit 2) E HAE HR0.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_tail B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _ Hst HC2 Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | apply wb10_corr_none; left; exact Hcc].
- let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek false (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_false_iff, Z.eqb_eq in Hcc.
  (* 0x8273c .. 0x8291c: len (> 8), b1, the trap 0x82918, then RT (a5 = 0) *)
  wb10a_run_to RSB_RT.
  all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
  wb10a_keep_tac.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SLit 2) E HAE HR0.
  pose proof (wb10a_off_bound (rsb_plen sh ps) (fst (fuzz_u16 [b1])) ltac:(lia)) as Hob.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_RT B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _
      (8 + fst (fuzz_u16 [b1]) mod (rsb_plen sh ps - 8)) HRT Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | apply wb10a_m_rt_short; [exact Hcc | lia | cbn; lia] | lia | lia].
Qed.

(* ---- len >= 9, |r| = 1: only c is read ---- *)
Lemma wb10a_c1 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps (c : byte),
  rsb_start_M01 rsegs B cx rest -> rsb_from_RT rsegs B MT cx POST rest -> rsb_from_C2 rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest [c] ly2 S2 W2 regs2 mem2 md2 -> 9 <= rsb_plen sh ps ->
  SRr rsegs W2 (cfg_at rsegs WB10_T regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c Hst HRT HC2 Hcut H9.
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
set (r := [c]) in *.
destruct (wb10a_ctx B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 Hst Hcut)
  as (H20 & H7 & H29 & H26 & Hinb & Hpp4 & Hppc & Hq & HLb & Hc1 & Hc2 & Hr63 & Hra).
pose proof Hcut as (HC & _).
pose proof HC as (HJ & _).
pose proof asan_consts as (C1 & _).
assert (Lr : length r = 1%nat) by reflexivity.
set (cur := rsb_cur rsegs cx rest r) in *.
remember (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) as E eqn:HE.
assert (HS : st_ok rsegs E (wb10a_ss 1 (SLit 1) 1 1 9 5440)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 WB10_T) mem2 (seg_rom rsegs)))).
{ subst E. apply (wb10a_entry B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 1 (SLit 1) 1 1 9 5440 Hst Hcut);
    [rewrite Lr; lia | lia | exact H29 | rewrite Lr; lia | lia | lia | lia]. }
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E7 : ew E 7 = Z_to_bv 64 (q_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact H7).
assert (E26 : ew E 26 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 (Z_to_bv 5 26) eq_refl); exact H26).
assert (E33 : ew E 33 = Z_to_bv 64 (bv_unsigned c)) by (subst E; reflexivity).
pose proof (Cursor.byte_range c) as Bc.
assert (HR0 : forall rr, getr regs2 rr = sv_denot E (sr_get (wb10a_sr (SLit 1)) rr))
  by (intros rr; exact (st_ok_restrict_reg rsegs (w_H W2) E _ _ rr HS)).
assert (HAE : env_agree 32 (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (Hra' : forall i, 0 <= i < 1 -> range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (cur + i) 1)
  by (intros i Hi; apply Hra; rewrite Lr; lia).
clear HE.
unfold cfg_at. change (w64 WB10_T) with (Z_to_bv 64 WB10_T).
(* 0x8270c .. 0x82738: the byte c *)
wb10a_run.
all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
wb10a_keep_tac.
wb10a_branch Hc.
- (* c mod 16 <> 15 -> 0x82a14 *)
  let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek true (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_true_iff, Z.eqb_neq in Hcc.
  wb10a_run_to 0x82a14. { awr_ok_tac. }
  wb10a_keep_tac.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SLit 1) E HAE HR0.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_tail B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _ Hst HC2 Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | apply wb10_corr_none; left; exact Hcc].
- let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek false (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_false_iff, Z.eqb_eq in Hcc.
  (* 0x8273c .. 0x8291c: len (> 8), the join 0x82904, the trap 0x82918, then RT (a5 = 0) *)
  wb10a_run_to RSB_RT.
  all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
  wb10a_keep_tac.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SLit 1) E HAE HR0.
  pose proof (wb10a_off_bound (rsb_plen sh ps) (fst (fuzz_u16 [])) ltac:(lia)) as Hob.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_RT B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _
      (8 + fst (fuzz_u16 []) mod (rsb_plen sh ps - 8)) HRT Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | apply wb10a_m_rt_short; [exact Hcc | lia | cbn; lia] | lia | lia].
Qed.

(* ---- len = 8, |r| >= 1: c is read; c mod 16 = 15 goes to the second request through `bltu s6,9` ---- *)
Lemma wb10a_c8 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps (c : byte) r1,
  rsb_start_M01 rsegs B cx rest -> rsb_from_C2 rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest (c :: r1) ly2 S2 W2 regs2 mem2 md2 -> rsb_plen sh ps = 8 ->
  SRr rsegs W2 (cfg_at rsegs WB10_T regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c r1 Hst HC2 Hcut H8.
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
set (r := c :: r1) in *.
destruct (wb10a_ctx B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 Hst Hcut)
  as (H20 & H7 & H29 & H26 & Hinb & Hpp4 & Hppc & Hq & HLb & Hc1 & Hc2 & Hr63 & Hra).
pose proof Hcut as (HC & _).
pose proof HC as (HJ & _).
pose proof asan_consts as (C1 & _).
assert (Lr : length r = S (length r1)) by reflexivity.
set (cur := rsb_cur rsegs cx rest r) in *.
remember (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) as E eqn:HE.
assert (HS : st_ok rsegs E (wb10a_ss 1 (SOff 29 0) 1 (2 ^ 63) 8 8)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 WB10_T) mem2 (seg_rom rsegs)))).
{ subst E. apply (wb10a_entry B MT cx rest sh ps r ly2 S2 W2 regs2 mem2 md2 1 (SOff 29 0) 1 (2 ^ 63) 8 8 Hst Hcut);
    [rewrite Lr; lia | lia | | rewrite Lr; lia | lia | lia | lia].
  rewrite (wb10_den_atom _ 29 (Z.of_nat (length r))); [exact H29|].
  rewrite (ew_Ereg_nat regs2 _ 29 (Z_to_bv 5 29) eq_refl). exact H29. }
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E7 : ew E 7 = Z_to_bv 64 (q_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact H7).
assert (E26 : ew E 26 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 (Z_to_bv 5 26) eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 (rsb_plen sh ps)) by (subst E; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (bv_unsigned c)) by (subst E; reflexivity).
pose proof (Cursor.byte_range c) as Bc.
assert (HR0 : forall rr, getr regs2 rr = sv_denot E (sr_get (wb10a_sr (SOff 29 0)) rr))
  by (intros rr; exact (st_ok_restrict_reg rsegs (w_H W2) E _ _ rr HS)).
assert (HAE : env_agree 32 (Ereg regs2 (wb10a_extra (rsb_plen sh ps) r)) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (Hra' : forall i, 0 <= i < 1 -> range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (cur + i) 1)
  by (intros i Hi; apply Hra; rewrite Lr; lia).
clear HE.
unfold cfg_at. change (w64 WB10_T) with (Z_to_bv 64 WB10_T).
(* 0x8270c .. 0x82738: the byte c *)
wb10a_run.
all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
wb10a_keep_tac.
wb10a_branch Hc.
- (* c mod 16 <> 15 -> 0x82a14 *)
  let Ek := wb10a_env_of Hc in
  pose proof (wb10a_br_c Ek true (bv_unsigned c) Hc ltac:(wb10a_ew E33) Bc) as Hcc.
  apply negb_true_iff, Z.eqb_neq in Hcc.
  wb10a_run_to 0x82a14. { awr_ok_tac. }
  wb10a_keep_tac.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SOff 29 0) E HAE HR0.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_tail B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _ Hst HC2 Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | apply wb10_corr_none; left; exact Hcc].
- (* 0x8273c .. 0x82750: len = 8 -> 0x82a24 with s6 = len *)
  wb10a_run_to 0x82a24.
  all: try solve [wb10a_ob HJ Hinb E20 E7 E26 KE Hra' | awr_ok_tac].
  wb10a_keep_tac.
  lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
    assert (R22 : getr (ms_regs msf) (Z_to_bv 5 22) = w64 (q_len (x_e cx)))
      by (rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ msf (Z_to_bv 5 22) HSf); wb10_sr_eval; rewrite Hq;
          exact (wb10_den_atom Ef 32 _ ltac:(wb10a_ew E32)))
  end.
  wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) r) (SOff 29 0) E HAE HR0.
  lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (wb10a_end_tail8 B MT cx POST rest sh ps r ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _ Hst HC2 Hcut HJ)
  end; [wb10a_kio | exact KE | exact RK | exact R22 | apply wb10_corr_none; right; lia].
Qed.

(* ---- nothing left of the input ---- *)
Lemma wb10a_c0 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps,
  rsb_start_M01 rsegs B cx rest -> rsb_from_C2 rsegs B MT cx POST rest ->
  wb10_cut_T B MT cx sh ps rest [] ly2 S2 W2 regs2 mem2 md2 ->
  SRr rsegs W2 (cfg_at rsegs WB10_T regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps Hst HC2 Hcut.
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (wb10a_ctx B MT cx rest sh ps [] ly2 S2 W2 regs2 mem2 md2 Hst Hcut)
  as (H20 & H7 & H29 & H26 & Hinb & Hpp4 & Hppc & Hq & HLb & Hc1 & Hc2 & Hr63 & Hra).
pose proof Hcut as (HC & _).
pose proof HC as (HJ & _).
remember (Ereg regs2 (wb10a_extra (rsb_plen sh ps) [])) as E eqn:HE.
assert (HS : st_ok rsegs E (wb10a_ss 0 (SLit 0) 0 0 8 5440)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 WB10_T) mem2 (seg_rom rsegs)))).
{ subst E. apply (wb10a_entry B MT cx rest sh ps [] ly2 S2 W2 regs2 mem2 md2 0 (SLit 0) 0 0 8 5440 Hst Hcut);
    [cbn; lia | lia | exact H29 | cbn; lia | lia | lia | lia]. }
assert (HR0 : forall rr, getr regs2 rr = sv_denot E (sr_get (wb10a_sr (SLit 0)) rr))
  by (intros rr; exact (st_ok_restrict_reg rsegs (w_H W2) E _ _ rr HS)).
assert (HAE : env_agree 32 (Ereg regs2 (wb10a_extra (rsb_plen sh ps) [])) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
clear HE.
unfold cfg_at. change (w64 WB10_T) with (Z_to_bv 64 WB10_T).
(* 0x8270c beqz t4 -> 0x82a14 *)
wb10a_run_to 0x82a14. { awr_ok_tac. }
wb10a_keep_tac.
wb10a_fin regs2 W2 (wb10a_extra (rsb_plen sh ps) []) (SLit 0) E HAE HR0.
lazymatch goal with HSf : st_ok _ _ _ (restrict _ ?msf) |- _ =>
  apply (wb10a_end_tail B MT cx POST rest sh ps [] ly2 S2 W2 regs2 mem2 md2 (ms_regs msf) (ms_mem msf) _ Hst HC2 Hcut HJ)
end; [wb10a_kio | exact KE | exact RK | apply wb10_corr_none_nil].
Qed.

(* ======================================== 5. the piece's second half ======================================== *)
Theorem wb10_arms : wb10_arms_stmt B MT.
Proof.
unfold wb10_arms_stmt, wb10_from_T.
intros cx POST rest Hst HR HRT HC2 ly2 S2 W2 regs2 mem2 md2 sh ps r Hcut.
destruct r as [|c r1].
- exact (wb10a_c0 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps Hst HC2 Hcut).
- pose proof (wb10a_ctx B MT cx rest sh ps (c :: r1) ly2 S2 W2 regs2 mem2 md2 Hst Hcut)
    as (_ & _ & _ & _ & _ & _ & _ & _ & HLb & _).
  destruct (Z.eq_dec (rsb_plen sh ps) 8) as [H8|H8].
  + exact (wb10a_c8 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c r1 Hst HC2 Hcut H8).
  + assert (H9 : 9 <= rsb_plen sh ps) by lia.
    destruct r1 as [|b1 [|b2 [|nb r4]]].
    * exact (wb10a_c1 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c Hst HRT HC2 Hcut H9).
    * exact (wb10a_c2 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c b1 Hst HRT HC2 Hcut H9).
    * exact (wb10a_c3 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c b1 b2 Hst HRT HC2 Hcut H9).
    * exact (wb10a_c4 cx POST rest ly2 S2 W2 regs2 mem2 md2 sh ps c b1 b2 nb r4 Hst (HR 0%nat) HRT HC2 Hcut H9).
Qed.
End c.

Print Assumptions wb10_arms.
