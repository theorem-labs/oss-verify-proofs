(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 697 of its 763 lines of code are new or changed and 1858 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 2932 of its 3021 lines of code are new or changed and 674 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4a: Lemma lc_op4a_ok : lc_op4a_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment OP4A of the image-B walk of LLVMFuzzerTestOneInput (listing lib/B/Prog/DgnTransportBList.v, offsets from
   0x812a0), from the cut lc_st_arm cx op 4 (+0x630) to lc_st_subr (+0x12bc) or lc_st_subt (+0xfa4).

   What the code does.
     +0x630 .. +0x664  c's four shadow bytes (frame shadow 4 .. 7) := 0; g_s from 112(s1), s5 = the `lw` of
                       g_s.queued (g_s + 18144, sign-extended), s6 = OW; `jal __asan_memset` (OW, 0, 304);
     +0x668 .. +0x678  `jal __asan_memset` (GOT, 0, 224);
     +0x67c .. +0x6a0  the byte g_fail_next (its page at 184(s1)), OW.desk_off := -1 (OW + 232), M.fail :=
                       g_fail_next (M from 168(s1), M + 88); `jal __asan_memset` (c = s4, 0, 32);
     +0x6a4 .. +0xad8  stage K, the kind and address bytes at the cursor s8 (bytes left s11 = s7 - 1): `beqz s11`
                       (+0x944: none), else the UBSan cursor test and the checked load of the kind byte (shadow test
                       +0x6c4, slow path +0x16dc, report 0x82f1c), `bne s7, 2`, the UBSan cursor test +0xab4 and the
                       checked load of the address byte (+0xac0); a1 / a2 the two bytes, s6 = 1, s7 / s8 the cursor;
     +0xad8 .. +0x12b8 stage D: the key ((kind mod 9 + 1) << 16 | address) at c + 28, `beqz s7` (no byte left),
                       else the checked load of the display byte; g_raw (its page at 104(s1)), c + 25 := display & 1,
                       `beqz g_raw`: SUBT (+0xd14 / +0xf94: 24(s1) := s5, s4 = 1, s9 / s6 the cursor) or SUBR (the
                       length word's low byte +0xb60 and high byte +0x12a0, +0x12b4 .. +0x12b8: a1 = the word).

   How it is proved. Symbolic runs of lib/B/Prog/DgnTransportBPaLib.v over the G journal (TransportGRunB.v
   paj_run_x / paj_run_to_x), each from a fresh state whose atoms are the registers at its pc, and the three calls
   of __asan_memset through lib/A/Prog/TransportGCg.v gx_intrin_at (OW and GOT in G, their shadow from receive_cg.v
   trans_recv_cells over a cover list; c in the own class-2 frame, its shadow bytes 4 .. 7 zero after the first
   run). Stage K is split by the bytes left before the op byte (1: op4_k1; 2: op4_k2; 3 or more: op4_k3) and stage D
   by the bytes left after the key bytes (0 .. 3 or more: op4_d0 .. op4_d3); every run is cut at a checked load's
   shadow test, the slow path's `bge` is refuted from the shadow byte's alias fact (k_bge), and the loads of the input
   bytes are decided from a shadow entry of the input block (range_addressable_of_block), so no report call or trap
   is reached. The model: TCb.v op_begin_m is the two memsets and the two stores (TWorldG.v tw_fill_set /
   tw_write); segs.v lc_sub_kd / lc_raw_w / lc_raw_c4 are op_kd1 .. op_kd4 and op_raw0 .. op_raw2. op4_main composes
   the steps at the arm's machine state; lc_op4a_ok opens lc_st_arm and closes lc_sub_common, its core by
   LLVMFuzzerTestOneInput_st.v lc_core_kept_run. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB YF0x YE36.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TransportGNoticeB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 0. The offsets, the addresses and the symbolic states               *)
(* ------------------------------------------------------------------ *)

(* The pcs (offsets from the entry): the arm, the returns of the three calls of __asan_memset, the key join. *)
Definition O_ARM : Z := 0x630.
Definition O_R1 : Z := 0x668.
Definition O_R2 : Z := 0x67c.
Definition O_R3 : Z := 0x6a4.
Definition O_KEY : Z := 0xad8.
Lemma op4_offs : lo_arm 4 = O_ARM /\ LO_SUBR = 0x12bc /\ LO_SUBT = 0xfa4.
Proof. repeat split; reflexivity. Qed.

(* g_s.queued, and the pages of g_fail_next (184(s1)) and g_raw (104(s1)). *)
Definition Q_B : Z := TB_g_s + 18144.
Definition PG_GFN : Z := 0x5de728.
Definition PG_RAW : Z := 0x5de6ec.
Lemma op4_pages : transportb_hi 10 = PG_GFN /\ transportb_hi 8 = PG_RAW /\
  PG_GFN + 0x678 = TB_g_fail_next /\ PG_RAW + 0x674 = TB_g_raw.
Proof. repeat split; reflexivity. Qed.
Definition PTRF : Z := 140737479966720.

(* Run 1, +0x630 .. the call at +0x664: the frame's shadow bytes 4 .. 7 at s2 (atom 18, written); the spill
   112(s1) (atom 9) holding g_s; g_s.queued (4 bytes, atom 32). *)
Definition s1_R_sh : YP09.region := YP09.mkRegion (Some 18%nat) 4 8 4 8 [].
Definition s1_R_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 112 120 0 0 [YP09.mkChunk 112 (YP09.CVal 8 (SLit TB_g_s))].
Definition s1_R_q : YP09.region :=
  YP09.mkRegion None Q_B (Q_B + 4) 0 0 [YP09.mkChunk Q_B (YP09.CVal 4 (SOff 32 0))].
Definition s1_F : facts :=
  mkFacts [(18%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_s1 : sstate := mkSS O_ARM sr_atoms [s1_R_sh; s1_R_sp; s1_R_q] None s1_F.

(* Run 2, +0x668 .. the call at +0x678: no memory. *)
Definition ss_s2 : sstate := mkSS O_R1 sr_atoms [] None (mkFacts [] [] []).

(* Run 3, +0x67c .. the call at +0x6a0: s6 = OW pinned; the byte g_fail_next (atom 32), OW.desk_off (written), the
   spills 184(s1) (g_fail_next's page) and 168(s1) (M), M.fail (written). *)
Definition s3_regs : list sv := sr_set sr_atoms (Z_to_bv 5 22) (SLit TB_OW).
Definition s3_rs : smem :=
  [YP09.mkRegion None TB_g_fail_next (TB_g_fail_next + 1) 0 0
     [YP09.mkChunk TB_g_fail_next (YP09.CVal 1 (SOff 32 0))];
   YP09.mkRegion None (TB_OW + 232) (TB_OW + 236) (TB_OW + 232) (TB_OW + 236) [];
   YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (YP09.CVal 8 (SLit PG_GFN))];
   YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (YP09.CVal 8 (SLit TB_M))];
   YP09.mkRegion None (TB_M + 88) (TB_M + 92) (TB_M + 88) (TB_M + 92) []].
Definition s3_F : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 255 0)] [] [].
Definition ss_s3 : sstate := mkSS O_R2 s3_regs s3_rs None s3_F.
Definition B0 : Z * Z := (0, 0).

Section env. Context {rc : YM05.RunCeil}.
(* The valuation of a fresh state: the 32 registers, then the extra atoms. *)
Definition op_E (r : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transportb) (Ereg r extra).
Lemma op_ew : forall r extra n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (op_E r extra) n = YK11.getr r x.
Proof. intros r extra n x Hn. unfold op_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma op_ewx : forall r extra j, (j < 8)%nat -> ew (op_E r extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros r extra j Hj. unfold op_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma op_env : forall r extra, img_env (@pa_val _ transportb_listing PI_transportb) A_LIM (op_E r extra).
Proof. intros r extra. unfold op_E. apply Eimg_env. Qed.
Lemma op_base : @pa_val _ transportb_listing PI_transportb A_TEXT = transportb_text.
Proof. vm_compute. reflexivity. Qed.
Lemma op_objs : @pa_val _ transportb_listing PI_transportb (A_OBJ 12) = TB_OW /\
  @pa_val _ transportb_listing PI_transportb (A_OBJ 13) = TB_GOT.
Proof. split; vm_compute; reflexivity. Qed.
End env.

(* A word that wraps its value. *)
Lemma op_zbv : forall z, Z_to_bv 64 (zcanon z) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

(* A 32-bit value sign-extended is 0 exactly when it is 0. *)
Lemma op_swrap_z : forall g, 0 <= g < 2 ^ 32 ->
  (zcanon (bv_swrap 32 g) = 0 <-> g = 0) /\ (bv_swrap 32 g = 0 <-> g = 0).
Proof.
intros g Hg.
assert (Hs : bv_swrap 32 g = if g <? 2 ^ 31 then g else g - 2 ^ 32).
{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32 / 2) with (2 ^ 31) by reflexivity. replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity.
  destruct (Z.ltb_spec g (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (g + 2 ^ 31) with ((g - 2 ^ 31) + 1 * 2 ^ 32) by ring. rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
rewrite Hs. unfold zcanon, M64. destruct (Z.ltb_spec g (2 ^ 31)).
- rewrite Z.mod_small by lia. tauto.
- replace (g - 2 ^ 32) with ((g - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by ring.
  rewrite Z_mod_plus_full, Z.mod_small by lia. split; split; intros; lia.
Qed.

(* A multiple of 2 ^ s or'ed with a value below 2 ^ s is their sum. *)
Lemma op_lor_sh : forall s k y, 0 <= s -> 0 <= k -> 0 <= y < 2 ^ s -> Z.lor (k * 2 ^ s) y = k * 2 ^ s + y.
Proof.
intros s k y Hs Hk Hy.
assert (Hand : Z.land (k * 2 ^ s) y = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  rewrite <- Z.shiftl_mul_pow2 by lia. destruct (Z.lt_ge_cases i s) as [Hl | Hg].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec y 0) as [-> | Hy0]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 y i); [apply andb_false_r | lia |].
    assert (Hlg : Z.log2 y < s) by (apply Z.log2_lt_pow2; lia). lia. }
rewrite <- Z.lxor_lor by exact Hand. rewrite <- Z.add_nocarry_lxor by exact Hand. reflexivity.
Qed.
Lemma op_lor_shift : forall k y, 0 <= k -> 0 <= y < 65536 -> Z.lor (k * 65536) y = k * 65536 + y.
Proof. intros k y Hk Hy. exact (op_lor_sh 16 k y ltac:(lia) Hk Hy). Qed.

Lemma op_key_val : forall kb ab, 0 <= kb < 256 -> 0 <= ab < 256 ->
  DSpec.KEY (kb mod 9 + 1) ab = (kb mod 9 + 1) * 65536 + ab /\ 0 <= DSpec.KEY (kb mod 9 + 1) ab < 2 ^ 32.
Proof.
intros kb ab Hk Ha. unfold DSpec.KEY.
change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia. rewrite (Z.mod_small ab) by lia.
pose proof (Z.mod_pos_bound kb 9 ltac:(lia)).
rewrite op_lor_shift by lia. lia.
Qed.

(* The model's fuzz_u8 on a cursor with bytes left / with none. *)
Lemma op_u8 : forall D off n, n <> 0 ->
  TOP.fuzz_u8_m D (TOP.FuzzIn off n) = (TOP.FuzzIn (off + 1) (n - 1), DSpec.at8 D (Z.to_nat off)).
Proof.
intros D off n Hn. unfold TOP.fuzz_u8_m. cbn [TOP.fi_n TOP.fi_off]. rewrite (proj2 (Z.eqb_neq n 0) Hn). reflexivity.
Qed.
Lemma op_u80 : forall D off n, n = 0 -> TOP.fuzz_u8_m D (TOP.FuzzIn off n) = (TOP.FuzzIn off n, 0).
Proof. intros D off n Hn. subst n. reflexivity. Qed.

(* segs.v lc_sub_kd after the op byte, by the bytes left n0 before it: 1, 2, 3, 4 or more. *)
Lemma op_kd1 : forall D off0,
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 1)) = mkLsv (DSpec.KEY 1 0) 0 (TOP.FuzzIn (off0 + 1) 0).
Proof.
intros D off0. unfold lc_sub_kd, lc_oc. rewrite (op_u8 D off0 1) by lia. cbn [fst].
rewrite (op_u80 D (off0 + 1) (1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1) (1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1) (1 - 1)) by lia. cbv beta iota zeta. reflexivity.
Qed.
Lemma op_kd2 : forall D off0,
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 2)) =
  mkLsv (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) 0) 0 (TOP.FuzzIn (off0 + 2) 0).
Proof.
intros D off0. unfold lc_sub_kd, lc_oc. rewrite (op_u8 D off0 2) by lia. cbn [fst].
rewrite (op_u8 D (off0 + 1) (2 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1 + 1) (2 - 1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1 + 1) (2 - 1 - 1)) by lia. cbv beta iota zeta.
replace (off0 + 1 + 1) with (off0 + 2) by lia. reflexivity.
Qed.
Lemma op_kd3 : forall D off0,
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 3)) =
  mkLsv (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) (DSpec.at8 D (Z.to_nat (off0 + 2)))) 0
    (TOP.FuzzIn (off0 + 3) 0).
Proof.
intros D off0. unfold lc_sub_kd, lc_oc. rewrite (op_u8 D off0 3) by lia. cbn [fst].
rewrite (op_u8 D (off0 + 1) (3 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u8 D (off0 + 1 + 1) (3 - 1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1 + 1 + 1) (3 - 1 - 1 - 1)) by lia. cbv beta iota zeta.
replace (off0 + 1 + 1 + 1) with (off0 + 3) by lia. replace (off0 + 1 + 1) with (off0 + 2) by lia. reflexivity.
Qed.
Lemma op_kd4 : forall D off0 n0, 4 <= n0 ->
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 n0)) =
  mkLsv (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) (DSpec.at8 D (Z.to_nat (off0 + 2))))
    (Z.land (DSpec.at8 D (Z.to_nat (off0 + 3))) 1) (TOP.FuzzIn (off0 + 4) (n0 - 4)).
Proof.
intros D off0 n0 Hn. unfold lc_sub_kd, lc_oc. rewrite (op_u8 D off0 n0) by lia. cbn [fst].
rewrite (op_u8 D (off0 + 1) (n0 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u8 D (off0 + 1 + 1) (n0 - 1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u8 D (off0 + 1 + 1 + 1) (n0 - 1 - 1 - 1)) by lia. cbv beta iota zeta.
replace (off0 + 1 + 1 + 1 + 1) with (off0 + 4) by lia. replace (off0 + 1 + 1 + 1) with (off0 + 3) by lia.
replace (off0 + 1 + 1) with (off0 + 2) by lia. replace (n0 - 1 - 1 - 1 - 1) with (n0 - 4) by lia. reflexivity.
Qed.

(* The raw mode's length word (segs.v lc_raw_w / lc_raw_c4) after the display byte, by the bytes left. *)
Lemma op_raw0 : forall D off, lc_raw_w D (TOP.FuzzIn off 0) = 0 /\ lc_raw_c4 D (TOP.FuzzIn off 0) = TOP.FuzzIn off 0.
Proof. intros D off. split; reflexivity. Qed.
Lemma op_raw1 : forall D off,
  lc_raw_w D (TOP.FuzzIn off 1) = DSpec.at8 D (Z.to_nat off) /\
  lc_raw_c4 D (TOP.FuzzIn off 1) = TOP.FuzzIn (off + 1) 0.
Proof.
intros D off. unfold lc_raw_w, lc_raw_c4, TOP.fuzz_u16_m. rewrite (op_u8 D off 1) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off + 1) (1 - 1)) by lia. cbn [fst snd].
pose proof (DSpec.at8_range D (Z.to_nat off)) as R.
split; [|reflexivity]. rewrite Z.shiftl_0_l, Z.lor_0_r. apply Z.mod_small. lia.
Qed.
Lemma op_raw2 : forall D off n, 2 <= n ->
  lc_raw_w D (TOP.FuzzIn off n) = DSpec.at8 D (Z.to_nat off) + 256 * DSpec.at8 D (Z.to_nat (off + 1)) /\
  lc_raw_c4 D (TOP.FuzzIn off n) = TOP.FuzzIn (off + 2) (n - 2).
Proof.
intros D off n Hn. unfold lc_raw_w, lc_raw_c4, TOP.fuzz_u16_m. rewrite (op_u8 D off n) by lia. cbv beta iota zeta.
rewrite (op_u8 D (off + 1) (n - 1)) by lia. cbn [fst snd].
pose proof (DSpec.at8_range D (Z.to_nat off)) as R0. pose proof (DSpec.at8_range D (Z.to_nat (off + 1))) as R1.
split; [|f_equal; lia].
rewrite Z.shiftl_mul_pow2 by lia.
rewrite Z.lor_comm, (op_lor_sh 8 (DSpec.at8 D (Z.to_nat (off + 1))) (DSpec.at8 D (Z.to_nat off)) ltac:(lia)
  ltac:(lia) R0).
change (2 ^ 8) with 256 in *. rewrite Z.mod_small by lia. lia.
Qed.

(* The key the code computes from the kind byte (a1, atom 11) at +0xad8 .. +0xaf8: (b - 9 * ((57 * b) >> 9) + 1) & 255
   shifted by 16, then or'ed with the address byte (a2, atom 12); the value of the chunk the `sw` at +0xb00 stores. *)
Definition kexpr : sv :=
  SAlu ALU_SLL
    (SAlu ALU_AND
       (SAlu ALU_ADD
          (SAlu ALU_SUB
             (SAlu ALU_SUB (SOff 11 0) (SAlu ALU_SRL (SMd M_MUL (SOff 11 0) (SLit 57)) (SLit 9)))
             (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff 11 0) (SLit 57)) (SLit 9)) (SLit 3)))
          (SLit 1))
       (SLit 255))
    (SLit 16).
Definition kexprC : sv := SAlu ALU_OR kexpr (SOff 12 0).

Lemma kexpr_U : forall E kb, U E (SOff 11 0) = kb -> 0 <= kb < 256 -> U E kexpr = (kb mod 9 + 1) * 65536.
Proof.
intros E kb Hk Hb. unfold kexpr. rewrite !U_SAlu, !U_SMd, !U_SLit, Hk.
assert (Hn : exists m : nat, kb = Z.of_nat m /\ (m < 256)%nat) by (exists (Z.to_nat kb); lia).
destruct Hn as (m & -> & Hm). clear Hk Hb.
do 256 (destruct m as [|m]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma kexprC_U : forall E kb ab, U E (SOff 11 0) = kb -> U E (SOff 12 0) = ab -> 0 <= kb < 256 -> 0 <= ab < 256 ->
  U E kexprC = DSpec.KEY (kb mod 9 + 1) ab.
Proof.
intros E kb ab Hk Ha Hkb Hab. unfold kexprC. rewrite U_SAlu, (kexpr_U E kb Hk Hkb), Ha. cbn [zalu_raw].
pose proof (Z.mod_pos_bound kb 9 ltac:(lia)).
rewrite op_lor_shift by lia. destruct (op_key_val kb ab Hkb Hab) as (EK & BK). rewrite EK.
apply zcanon_id. unfold M64. lia.
Qed.

(* Byte j of c as segs.v lc_sub_common states it: cmd_struct (24 zeros) 0 display key. *)
Lemma op_cmd_nth : forall disp key (j : nat), 0 <= disp < 256 -> (j < 32)%nat ->
  nth j (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 disp key)) 0 =
  if (j =? 25)%nat then disp else if (j <? 28)%nat then 0 else YO0f.le_byte key 4 (j - 28).
Proof.
intros disp key j Hd Hj. unfold TW.zs, TOP.cmd_struct.
rewrite (nth_indep _ 0 (bv_unsigned (DSpec.b8 0)))
  by (rewrite length_map, !length_app, repeat_length, TWL.length_put; cbn [length]; lia).
rewrite map_nth.
destruct (Nat.lt_ge_cases j 28) as [Hl | Hg].
- rewrite app_assoc, app_nth1 by (rewrite length_app, repeat_length; cbn [length]; lia).
  do 28 (destruct j as [|j]; [cbn [nth repeat app Nat.eqb Nat.ltb Nat.leb];
    first [reflexivity | unfold DSpec.b8; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
           apply Z.mod_small; lia] |]).
  lia.
- rewrite app_assoc, app_nth2 by (rewrite length_app, repeat_length; cbn [length]; lia).
  rewrite length_app, repeat_length. cbn [length].
  replace (j - (24 + 4))%nat with (j - 28)%nat by lia.
  rewrite tw_le_byte_put by lia.
  destruct (Nat.eqb_spec j 25) as [E | E]; [lia|]. destruct (Nat.ltb_spec j 28) as [E2 | E2]; [lia|]. reflexivity.
Qed.

(* The frame's shadow map with c in scope differs from the one without only at bytes 4 .. 7, which are 0. *)
Lemma lf_shm_tf : forall i, 0 <= i < 32 -> ~ (4 <= i < 8) ->
  nth (Z.to_nat i) (lf_shm true false) 0 = nth (Z.to_nat i) (lf_shm false false) 0.
Proof.
intros i Hi Hn. assert (Hk : (Z.to_nat i < 32)%nat) by lia. assert (Hn' : ~ (4 <= Z.to_nat i < 8)%nat) by lia.
revert Hk Hn'. generalize (Z.to_nat i) as k. intros k Hk Hn'.
do 32 (destruct k as [|k]; [first [reflexivity | exfalso; lia] |]). lia.
Qed.
Lemma lf_shm_tc : forall i, 4 <= i < 8 -> nth (Z.to_nat i) (lf_shm true false) 0 = 0.
Proof.
intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

(* The shadow cells of the record that cover OW's and GOT's 64-byte hulls (receive_cg.v trans_recv_cells): the zero
   granules of OW, GOT and g_rx_len, g_rx_len's three guard granules, OW's first six guard granules after its payload
   and g_s's last four guard granules before GOT. *)
Definition cs_ow : list (Z * Z) :=
  trans_zgran TB_OW (TB_OW + TW.SZ_OW) ++ trans_zgran TB_g_rx_len (TB_g_rx_len + TW.SZ_g_rx_len) ++
  map (fun a => (a, 0xf9)) [TB_g_rx_len + 8; TB_g_rx_len + 16; TB_g_rx_len + 24; TB_OW + TW.SZ_OW;
    TB_OW + TW.SZ_OW + 8; TB_OW + TW.SZ_OW + 16; TB_OW + TW.SZ_OW + 24; TB_OW + TW.SZ_OW + 32; TB_OW + TW.SZ_OW + 40].
Definition cs_got : list (Z * Z) :=
  trans_zgran TB_GOT (TB_GOT + TW.SZ_GOT) ++ map (fun a => (a, 0xf9)) [TB_GOT - 32; TB_GOT - 24; TB_GOT - 16; TB_GOT - 8].
Lemma cs_ow_cover : trans_cs_cover cs_ow TB_OW 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cs_got_cover : trans_cs_cover cs_got TB_GOT 224 = true.
Proof. vm_compute. reflexivity. Qed.

Section cov. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma op_ow_sh : trans_recv_cells B -> trans_sh_any B TB_OW 304.
Proof.
intros (HZo & _ & HZr & HC). apply (trans_sh_any_cells B cs_ow); [|exact cs_ow_cover].
unfold cs_ow. apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZo | reflexivity]|].
apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZr | reflexivity]|].
apply trans_sh_cells_const; [|lia]. intros ly a Ha. pose proof (HC ly) as H.
cbn [In] in Ha. repeat (destruct Ha as [<- | Ha]; [tauto|]). destruct Ha.
Qed.
Lemma op_got_sh : trans_recv_cells B -> trans_sh_any B TB_GOT 224.
Proof.
intros (_ & HZg & _ & HC). apply (trans_sh_any_cells B cs_got); [|exact cs_got_cover].
unfold cs_got. apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZg | reflexivity]|].
apply trans_sh_cells_const; [|lia]. intros ly a Ha. pose proof (HC ly) as H.
cbn [In] in Ha. repeat (destruct Ha as [<- | Ha]; [tauto|]). destruct Ha.
Qed.

(* A register whose symbolic value is still its own atom holds its value at the run's start. *)
Lemma op_kr : forall E (regs : bvmap 5 word) extra (s : list sv) (v : word) (r : bv 5),
  (forall m, (m < 32)%nat -> ew E m = ew (op_E regs extra) m) ->
  v = sv_denot E (sr_get s r) -> sr_get s r = SOff (Z.to_nat (bv_unsigned r)) 0 -> v = YK11.getr regs r.
Proof.
intros E regs extra s v r HE Hv Hs. rewrite Hv, Hs. cbn [sv_denot].
pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite (HE (Z.to_nat (bv_unsigned r)) ltac:(lia)). rewrite (op_ew regs extra (Z.to_nat (bv_unsigned r)) r ltac:(lia)).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End cov.

(* A one-byte chunk of the literal 0 reads 0; a chunk of w bytes of e reads e's little-endian bytes. *)
Lemma op_chunk0 : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base_val E bopt + off) = Some 0.
Proof.
  intros E H m bopt lo hi wlo whi cs off (_ & _ & _ & Hcs) Hin.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  pose proof (val_of_chunk_any tfibsegs E _ _ off 1 (SLit 0) Hc ltac:(lia)) as V.
  change (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 1)) with 0 in V.
  change (N.to_nat 1) with 1%nat in V.
  exact (TransportGNoticeB.aview_of_val_mem1 H m _ 0 V ltac:(lia)).
Qed.
Lemma op_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac op_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac op_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "op_reg: no match for" T; fail
  end.

(* The region list of an awr obligation, computed. *)
Ltac op_awr_norm :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A read-only region: no writable byte. *)
Ltac op_awr_ro :=
  apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].

Section pc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HGX : gx_ok segs B TG.G_HARNESS_B.
Hypothesis HMS : @aintrin_realizes fx rc segs B OSet (transportb_sigma TB___asan_memset).
Hypothesis HRC : trans_recv_cells B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (ly : alayout) (S : astate) (W : world segs)
  (k : Z).
(* The class-2 frame F at position pos, owned by the journal; the realigned sp1. *)
Variables (F sp1 pos : Z).
Hypothesis HOWN : In (LF_CID, pos) own.
Hypothesis HFIN : In (LF_CID, pos) (frames S).
Hypothesis HFA : frame_addr ly LF_CID pos = F.
Hypothesis HF0 : 4096 <= F.
Hypothesis HF64 : F mod 64 = 0.
Hypothesis HFC : F + 256 <= alloc_ceiling.
Hypothesis HSPC : alloc_ceiling + 32432 <= sp1.
Hypothesis HSP47 : sp0 <= 2 ^ 47.
Hypothesis HSP32 : sp1 mod 32 = 0.
Hypothesis HSP0 : sp0 - 336 <= sp1 <= sp0 - 320.
Hypothesis HSP016 : sp0 mod 16 = 0.
Hypothesis HSTK : ESTACK + 336 <= STK.

Local Abbreviation J m md :=
  (@W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W m md k).
Local Abbreviation at_ pc r m md := (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) m (YK11.seg_rom segs)) md).
Local Abbreviation SHF := (SHADOW_OFF + F / 8).
Local Abbreviation rdv m := (aview segs (w_H W) m).

Lemma op_F8 : F / 8 = 8 * (F / 64) /\ F mod 8 = 0 /\ 512 <= F / 8 <= 2 ^ 44.
Proof.
pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. pose proof asan_consts as ((C1 & C2) & _).
split; [rewrite D at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia|].
split; [rewrite D; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.mod_mul; lia|].
split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia].
Qed.

(* The frame's bytes and shadow bytes present, at a memory of the journal. *)
Lemma op_frame_pres : forall m md, J m md ->
  (forall a, F <= a < F + 256 -> apresent (w_H W) m a) /\
  (forall i, 0 <= i < 32 -> apresent (w_H W) m (SHF + i)) /\ in_app F 256.
Proof.
intros m md HJ. pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_frames _ _ LAWS ly S W m md LF_CID pos HAR HFIN) as (_ & Happ & HFb & HFsh).
rewrite HFA in Happ, HFb, HFsh. change (fs_frame_bytes LF_CID) with 256 in Happ, HFb.
change (fs_frame_bytes LF_CID / 8) with 32 in HFsh.
split; [intros a Ha; exact (proj1 (HFb a Ha))|]. split; [intros i Hi; exact (proj1 (HFsh i Hi)) | exact Happ].
Qed.

(* Run 1's state at the arm. *)
Lemma s1_entry : forall regs mem q,
  YK11.getr regs 18 = w64 SHF -> YK11.getr regs 9 = w64 sp1 ->
  rdword (rdv mem) (sp1 + 112) = Some TB_g_s ->
  val_mem segs (mrestrict (w_H W) mem) Q_B 4 q -> 0 <= q < 2 ^ 32 ->
  (forall i, 4 <= i < 8 -> apresent (w_H W) mem (SHF + i)) ->
  st_ok_pi segs VAL (op_E regs [w64 q]) ss_s1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_ARM)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem q R18 R9 HSP HQV HQ HPS.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
set (E := op_E regs [w64 q]).
assert (U18 : bv_unsigned (ew E 18) = SHF)
  by (unfold E; rewrite (op_ew regs _ 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (op_ew regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 q) by (unfold E; exact (op_ewx regs _ 0 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = q) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_s1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks s1_R_sh s1_R_sp s1_R_q base_val];
    rewrite ?U18, ?U9.
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HPS. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 112 8 (SLit TB_g_s) TB_g_s); [reflexivity | unfold TB_g_s; cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword segs _ _ _ _ HSP).
  + split; [unfold Q_B, TB_g_s; lia|]. split; [unfold Q_B, TB_g_s; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 Q_B 4 (SOff 32 0) q); [| cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HQV].
    cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, s1_R_sh, s1_R_sp, s1_R_q.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold Q_B, TB_g_s, SHADOW_OFF in *. repeat split; first [exact I | lia].
- unfold s1_F, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U9, U32.
  change (2 ^ 3) with 8. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  assert (M8 : SHF mod 8 = 0).
  { rewrite F8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
    apply Z.mod_mul. lia. }
  unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* An image object's atom denotes its address. *)
Lemma op_atom_obj : forall E (i : nat) v, img_env VAL A_LIM E -> VAL (A_OBJ i) = v -> 0 <= v < 2 ^ 64 ->
  (A_OBJ i < A_LIM)%nat -> sv_denot E (SOff (A_OBJ i) 0) = w64 v.
Proof.
intros E i v HE Hv Hr Hl. cbn [sv_denot]. rewrite (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT in *; lia)), Hv.
rewrite Z.add_0_r. reflexivity.
Qed.

(* The callee-saved registers, case by case. *)
Lemma op_saved_cases : forall (P : Z -> Prop), P 2 -> P 3 -> P 4 -> P 8 -> P 9 -> P 18 -> P 19 -> P 20 -> P 21 ->
  P 22 -> P 23 -> P 24 -> P 25 -> P 26 -> P 27 -> forall r, acallee_saved r -> P r.
Proof.
intros P H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
             r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc]; [assumption|]). subst r. assumption.
Qed.

(* __asan_memset (d, 0, n) at sp1 through TransportGCg.v gx_intrin_at: [d, d + n) := 0, every other byte but the
   ESTACK bytes below sp1 kept, the callee-saved registers kept. *)
Lemma op_memset : forall regsT memT mdc d n raw (Q : world segs -> config -> Prop),
  J memT mdc ->
  YK11.getr regsT 10 = w64 d -> YK11.getr regsT 11 = w64 0 -> YK11.getr regsT 12 = w64 n ->
  YK11.getr regsT 2 = w64 sp1 -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
  (forall a, d <= a < d + n ->
     (awr_byte STK sp0 FP (ablocks B ly0 S0) (ablocks B ly S) ly own a /\ ~ (sp1 - ESTACK <= a < sp1)) \/
     inG TG.G_HARNESS_B a) ->
  amem_range d n -> range_addressable (rdv memT) SHADOW_OFF d n -> shadow_hull_vis (rdv memT) d n ->
  (forall regs2 mem2 md2, J mem2 md2 -> aregs_preserved regsT regs2 ->
     (forall i, 0 <= i < n -> rdv mem2 (d + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp1 - ESTACK <= a < sp1) -> rdv mem2 a = rdv memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     SRr segs W (mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___asan_memset)) memT (YK11.seg_rom segs))
    mdc) Q.
Proof.
intros regsT memT mdc d n raw Q HJ R10 R11 R12 R2 R3 R4 R1 Hraw Hn Hd0 Hdn Hwr Hamr Hra Hhull HK.
assert (USP : spZ regsT = sp1).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. pose proof asan_consts as ((C1 & C2) & _). lia. }
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OSet
    (transportb_sigma TB___asan_memset) HMS TG.G_HARNESS_B W regsT memT STK sp0 FP ly0 S0 W0 mem0 md0 own ly S mdc k
    d 0 n (sp1 - sp0) raw HGX G_HARNESS_B_rw HJ R10 R11 R12).
  - exact Hn.
  - exact Hd0.
  - exact Hdn.
  - rewrite USP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite HSP32, Z.add_0_r in D1. rewrite HSP016, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - exact Hraw.
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. rewrite USP. exact Hwr.
  - exact Hamr.
  - exact Hra.
  - intros _. exact Hhull.
  - exact I. }
cbv beta. intros Wm c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
apply (HK regs2 mem2 md2 HJ2 HP2).
- intros i Hi. rewrite (Hset2 i Hi). reflexivity.
- intros a Ha H1 H2. apply Heff2; [exact Ha | exact H1 | lia].
- exact Hgr2.
Qed.

(* Run 1 and __asan_memset (OW, 0, 304): from the arm to the memset's return +0x668. *)
Lemma op4_s1 : forall regs mem md q (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 SHF ->
  rdword (rdv mem) (sp1 + 112) = Some TB_g_s ->
  val_mem segs (mrestrict (w_H W) mem) Q_B 4 q -> 0 <= q < 2 ^ 32 ->
  (forall regs2 mem2 md2, J mem2 md2 ->
     YK11.getr regs2 21 = Z_to_bv 64 (bv_swrap 32 q) -> YK11.getr regs2 22 = w64 TB_OW ->
     (forall r, acallee_saved r -> r <> 21 -> r <> 22 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
     (forall i, 4 <= i < 8 -> rdv mem2 (SHF + i) = Some 0) ->
     (forall i, 0 <= i < 304 -> rdv mem2 (TB_OW + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (SHF + 4 <= a < SHF + 8) -> ~ (TB_OW <= a < TB_OW + 304) ->
        ~ (sp1 - ESTACK <= a < sp1) -> rdv mem2 a = rdv mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     SRr segs W (at_ O_R1 regs2 mem2 md2) Q) ->
  SRr segs W (at_ O_ARM regs mem md) Q.
Proof.
intros regs mem md q Q HJ R2 R3 R4 R9 R18 HSP HQV HQ HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
destruct (op_frame_pres mem md HJ) as (_ & HFsh & _).
pose proof (s1_entry regs mem q R18 R9 HSP HQV HQ ltac:(intros i Hi; apply HFsh; lia)) as HS.
set (E0 := op_E regs [w64 q]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (U18 : bv_unsigned (ew E0 18) = SHF)
  by (unfold E0; rewrite (op_ew regs _ 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (unfold E0; rewrite (op_ew regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E0 32 = w64 q) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
paj_run_tok RUN HS HJ SHOK B0.
{ op_awr_norm.
  eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18 in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID / 8) with 32. lia. }
  op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHF + 4 <= a < SHF + 8) -> rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHF + 4 <= x < SHF + 8) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta. op_win Hiw Hx ltac:(rewrite ?U18 in Hx; lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 8 -> rdv (ms_mem ms) (SHF + i) = Some 0).
{ intros i Hi. rewrite <- U18.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi' as [-> | [-> | [-> | ->]]];
  apply (op_chunk0 E0 (w_H W) (ms_mem ms) (Some 18%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pmkst HS.
op_reg HS (Z_to_bv 5 10) (w64 TB_OW) Q10
  ltac:(exact (op_atom_obj _ 12 TB_OW HEI (proj1 op_objs) ltac:(unfold TB_OW; lia) ltac:(unfold A_OBJ, A_LIM; lia))).
op_reg HS (Z_to_bv 5 22) (w64 TB_OW) Q22
  ltac:(exact (op_atom_obj _ 12 TB_OW HEI (proj1 op_objs) ltac:(unfold TB_OW; lia) ltac:(unfold A_OBJ, A_LIM; lia))).
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 12) (w64 304) Q12 ltac:(reflexivity).
op_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + O_R1)) Q1 ltac:(apply codeptr_val; exact HEI).
op_reg HS (Z_to_bv 5 21) (Z_to_bv 64 (bv_swrap 32 q)) Q21
  ltac:(rewrite denot_lit_U, U_SExt, U_SOff, E32; unfold w64; rewrite unsigned_lit_small by lia;
        rewrite Z.add_0_r, (zcanon_id q) by (unfold M64; lia); rewrite Z.mod_small by lia; apply op_zbv).
assert (KR : forall r, acallee_saved r -> r <> 21 -> r <> 22 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 q] (ss_regs ssx) _ r (fun m _ => eq_refl)
      (st_ok_restrict_reg segs Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H21 H22;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity]. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Qx) end.
apply (op_memset (ms_regs ms) (ms_mem ms) md1 TB_OW 304 (Z_to_bv 64 (BASE + O_R1)) Q HJ Q10 Q11 Q12
  (eq_trans (KR 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R2)
  (eq_trans (KR 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R3)
  (eq_trans (KR 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R4) Q1).
- apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold O_R1; lia | reflexivity].
- lia.
- unfold TB_OW; lia.
- unfold TB_OW; lia.
- intros a Ha. right. unfold inG. apply Exists_exists. exists (TB_OW, TW.SZ_OW).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
- left. unfold kLowMemEnd, TB_OW. lia.
- exact (proj1 (op_ow_sh B HRC ly S W (ms_mem ms) md1 (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
- exact (proj2 (op_ow_sh B HRC ly S W (ms_mem ms) md1 (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
- intros regs2 mem2 md2 HJ2 HP2 HZ2 HK2 HG2.
  apply (HK regs2 mem2 md2 HJ2).
  + exact (eq_trans (HP2 21 ltac:(unfold acallee_saved; lia)) Q21).
  + exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) Q22).
  + intros r Hr H21 H22. exact (eq_trans (HP2 r Hr) (KR r Hr H21 H22)).
  + intros i Hi. rewrite HK2 by (unfold ESTACK, SHADOW_OFF, TB_OW in *; lia). exact (ZS1 i Hi).
  + intros i Hi. exact (HZ2 i Hi).
  + intros a Ha H1 H2 H3. rewrite (HK2 a Ha H2 H3). exact (KR1 a Ha H1).
  + intros a Ha. exact (HG2 a (GA1 a Ha)).
Qed.

(* Run 2's state at +0x668: no memory. *)
Lemma s2_entry : forall regs mem,
  st_ok_pi segs VAL (op_E regs []) ss_s2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R1)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem. rewrite restrict_mkst_fx. unfold ss_s2.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- exact (conj I (conj I I)).
Qed.

(* Run 2 and __asan_memset (GOT, 0, 224): from +0x668 to the memset's return +0x67c. *)
Lemma op4_s2 : forall regs mem md (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  (forall regs2 mem2 md2, J mem2 md2 ->
     (forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
     (forall i, 0 <= i < 224 -> rdv mem2 (TB_GOT + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (TB_GOT <= a < TB_GOT + 224) -> ~ (sp1 - ESTACK <= a < sp1) ->
        rdv mem2 a = rdv mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     SRr segs W (at_ O_R2 regs2 mem2 md2) Q) ->
  SRr segs W (at_ O_R1 regs mem md) Q.
Proof.
intros regs mem md Q HJ R2 R3 R4 HK.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (s2_entry regs mem) as HS.
set (E0 := op_E regs []) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
paj_run_tok RUN HS HJ SHOK B0.
{ op_awr_norm. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hiw Hx. cbv beta. op_win Hiw Hx ltac:(lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
op_reg HS (Z_to_bv 5 10) (w64 TB_GOT) Q10
  ltac:(exact (op_atom_obj _ 13 TB_GOT HEI (proj2 op_objs) ltac:(unfold TB_GOT; lia) ltac:(unfold A_OBJ, A_LIM; lia))).
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 12) (w64 224) Q12 ltac:(reflexivity).
op_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + O_R2)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (KR : forall r, acallee_saved r -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [] (ss_regs ssx) _ r (fun m _ => eq_refl)
      (st_ok_restrict_reg segs Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; apply HKR; vm_compute; reflexivity. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Qx) end.
apply (op_memset (ms_regs ms) (ms_mem ms) md1 TB_GOT 224 (Z_to_bv 64 (BASE + O_R2)) Q HJ Q10 Q11 Q12
  (eq_trans (KR 2 ltac:(unfold acallee_saved; lia)) R2)
  (eq_trans (KR 3 ltac:(unfold acallee_saved; lia)) R3)
  (eq_trans (KR 4 ltac:(unfold acallee_saved; lia)) R4) Q1).
- apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold O_R2; lia | reflexivity].
- lia.
- unfold TB_GOT; lia.
- unfold TB_GOT; lia.
- intros a Ha. right. unfold inG. apply Exists_exists. exists (TB_GOT, TW.SZ_GOT).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_GOT) | unfold in_zr, TW.SZ_GOT; cbn [fst snd]; lia].
- left. unfold kLowMemEnd, TB_GOT. lia.
- exact (proj1 (op_got_sh B HRC ly S W (ms_mem ms) md1 (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
- exact (proj2 (op_got_sh B HRC ly S W (ms_mem ms) md1 (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
- intros regs2 mem2 md2 HJ2 HP2 HZ2 HK2 HG2.
  apply (HK regs2 mem2 md2 HJ2).
  + intros r Hr. exact (eq_trans (HP2 r Hr) (KR r Hr)).
  + exact HZ2.
  + intros a Ha H1 H2. rewrite (HK2 a Ha H1 H2). exact (KR1 a Ha).
  + intros a Ha. exact (HG2 a (GA1 a Ha)).
Qed.

(* A byte of a value in memory, as the view reads it. *)
Lemma op_vm_av : forall (H : word -> bool) m a (n : nat) v (j : nat),
  val_mem segs (mrestrict H m) a n v -> (j < n)%nat -> aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v j Hv Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* A payload byte of a global is a byte of G; a byte of G lies in low memory and outside the frame. *)
Lemma op_inG_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma op_G_low : forall a, inG TG.G_HARNESS_B a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. exact (inG_low segs B transportb_segs_low _ a HGX Ha). Qed.
Lemma op_G_frame : forall m md, J m md -> forall a, inG TG.G_HARNESS_B a -> ~ (F <= a < F + 256).
Proof.
intros m md HJ a Ha Hf.
apply (frm_img segs B LAWS ly S W m md LF_CID pos a (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HFIN);
  [rewrite HFA; change (fs_frame_bytes LF_CID) with 256; lia|].
exact (trans_g_img a Ha).
Qed.

(* Run 3's state at +0x67c (s6 pinned). *)
Lemma s3_entry : forall regs mem gfn,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 TB_OW ->
  val_mem segs (mrestrict (w_H W) mem) TB_g_fail_next 1 gfn -> 0 <= gfn < 256 ->
  rdword (rdv mem) (sp1 + 184) = Some PG_GFN -> rdword (rdv mem) (sp1 + 168) = Some TB_M ->
  st_ok_pi segs VAL (op_E regs [w64 gfn]) ss_s3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R2)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem gfn R9 R22 HGV HGB H184 H168.
pose proof asan_consts as ((C1 & C2) & _).
set (E := op_E regs [w64 gfn]).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (op_ew regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 gfn) by (unfold E; exact (op_ewx regs _ 0 ltac:(lia))).
assert (H0 : st_ok_pi segs VAL E (mkSS O_R2 sr_atoms s3_rs None s3_F)
  (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R2)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold s3_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9.
    + split; [unfold TB_g_fail_next; lia|]. split; [unfold TB_g_fail_next; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TB_g_fail_next 1 (SOff 32 0) gfn); [| cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HGV].
      cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + split; [unfold TB_OW; lia|]. split; [unfold TB_OW; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw).
      apply (op_inG_row _ _ _ _ TMAP_B_OW). unfold TB_OW, TW.SZ_OW in *. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 184 8 (SLit PG_GFN) PG_GFN); [reflexivity | unfold PG_GFN; cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword segs _ _ _ _ H184).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 168 8 (SLit TB_M) TB_M); [reflexivity | unfold TB_M; cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword segs _ _ _ _ H168).
    + split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw).
      apply (op_inG_row _ _ _ _ TMAP_B_M). unfold TB_M, TW.SZ_M in *. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, s3_rs.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TB_g_fail_next, TB_OW, TB_M in *. repeat split; first [exact I | lia].
  - unfold s3_F, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
    assert (U32 : bv_unsigned (ew E 32) = gfn) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
    rewrite U32. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 22) TB_OW H0 R22 eq_refl).
Qed.

(* Run 3 and __asan_memset (c, 0, 32): from +0x67c to the memset's return +0x6a4. *)
Lemma op4_s3 : forall regs mem md gfn (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 (F + 32) -> YK11.getr regs 22 = w64 TB_OW ->
  val_mem segs (mrestrict (w_H W) mem) TB_g_fail_next 1 gfn -> 0 <= gfn < 256 ->
  rdword (rdv mem) (sp1 + 184) = Some PG_GFN -> rdword (rdv mem) (sp1 + 168) = Some TB_M ->
  (forall i, 4 <= i < 8 -> rdv mem (SHF + i) = Some 0) ->
  (forall regs2 mem2 md2, J mem2 md2 ->
     (forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
     (forall j, (j < 4)%nat -> rdv mem2 (TB_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte 4294967295 4 j)) ->
     (forall j, (j < 4)%nat -> rdv mem2 (TB_M + 88 + Z.of_nat j) = Some (YO0f.le_byte gfn 4 j)) ->
     (forall i, 0 <= i < 32 -> rdv mem2 (F + 32 + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 232 <= a < TB_OW + 236) -> ~ (TB_M + 88 <= a < TB_M + 92) ->
        ~ (F + 32 <= a < F + 64) -> ~ (sp1 - ESTACK <= a < sp1) -> rdv mem2 a = rdv mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     SRr segs W (at_ O_R3 regs2 mem2 md2) Q) ->
  SRr segs W (at_ O_R2 regs mem md) Q.
Proof.
intros regs mem md gfn Q HJ R2 R3 R4 R9 R20 R22 HGV HGB H184 H168 HZS HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (s3_entry regs mem gfn R9 R22 HGV HGB H184 H168) as HS.
set (E0 := op_E regs [w64 gfn]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (E32 : ew E0 32 = w64 gfn) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
paj_run_tok RUN HS HJ SHOK B0.
{ op_awr_norm. op_awr_ro.
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    apply (op_inG_row _ _ _ _ TMAP_B_OW). unfold TB_OW, TW.SZ_OW in *. lia. }
  op_awr_ro. op_awr_ro.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  apply (op_inG_row _ _ _ _ TMAP_B_M). unfold TB_M, TW.SZ_M in *. lia. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 232 <= a < TB_OW + 236) -> ~ (TB_M + 88 <= a < TB_M + 92) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 232 <= x < TB_OW + 236) \/ (TB_M + 88 <= x < TB_M + 92)) HFr);
    [| exact Ha | intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hiw Hx. cbv beta. op_win Hiw Hx ltac:(unfold TB_OW, TB_M; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
pose proof (st_ok_region_nth _ _ _ 4 _ HS eq_refl) as RG4. cbn [ms_mem restrict] in RG4.
pose proof (op_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6237640 4 (SLit 18446744073709551615) RG1
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VOW.
pose proof (op_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6155832 4 (SOff 32 0) RG4
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VM.
cbn [base_val] in VOW, VM.
change (bv_unsigned (sv_denot E0 (SLit 18446744073709551615)) mod 2 ^ (8 * Z.of_N 4)) with 4294967295 in VOW.
replace (bv_unsigned (sv_denot E0 (SOff 32 0)) mod 2 ^ (8 * Z.of_N 4)) with gfn in VM
  by (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; unfold w64; rewrite unsigned_lit_small by lia;
      change (2 ^ (8 * Z.of_N 4)) with 4294967296; rewrite Z.mod_small by lia; reflexivity).
change (N.to_nat 4) with 4%nat in VOW, VM.
clear HF HFr HG RG1 RG4.
destruct (op_frame_pres (ms_mem ms) md1 HJ) as (_ & HFsh1 & Happ).
pmkst HS.
op_reg HS (Z_to_bv 5 10) (w64 (F + 32)) Q10
  ltac:(cbn [sv_denot]; unfold E0; rewrite (op_ew regs [w64 gfn] 20 20%bv eq_refl), R20, Z.add_0_r; unfold w64;
        rewrite unsigned_lit_small by lia; reflexivity).
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 12) (w64 32) Q12 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 22) (w64 TB_OW) Q22 ltac:(reflexivity).
op_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + O_R3)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (KR : forall r, acallee_saved r -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 gfn] (ss_regs ssx) _ r (fun m _ => eq_refl)
      (st_ok_restrict_reg segs Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases;
    first [apply HKR; vm_compute; reflexivity | exact (eq_trans Q22 (eq_sym R22))]. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Qx) end.
apply (op_memset (ms_regs ms) (ms_mem ms) md1 (F + 32) 32 (Z_to_bv 64 (BASE + O_R3)) Q HJ Q10 Q11 Q12
  (eq_trans (KR 2 ltac:(unfold acallee_saved; lia)) R2)
  (eq_trans (KR 3 ltac:(unfold acallee_saved; lia)) R3)
  (eq_trans (KR 4 ltac:(unfold acallee_saved; lia)) R4) Q1).
- apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold O_R3; lia | reflexivity].
- lia.
- lia.
- lia.
- intros a Ha. left. split.
  + unfold awr_byte. right; right; right. unfold in_frames. exists LF_CID, pos. split; [exact HOWN|].
    left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia.
  + unfold ESTACK. lia.
- exact (amem_range_sub_app F 256 (F + 32) 32 Happ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
- apply (TGNA.frame_ra_zero _ F (F + 32) 32 4 8); [lia | exact F8m | lia | lia |].
  intros i Hi. rewrite KR1 by (unfold TB_OW, TB_M, SHADOW_OFF in *; lia). exact (HZS i Hi).
- apply (TGNA.frame_hull_vis _ F 256 (F + 32) 32); [lia | exact HF64 | reflexivity | lia | lia | lia |].
  intros i Hi. apply CanKit.can_aview_vis. exact (HFsh1 i Hi).
- intros regs2 mem2 md2 HJ2 HP2 HZ2 HK2 HG2.
  assert (OUTW : forall a, inG TG.G_HARNESS_B a -> ~ (F + 32 <= a < F + 64) /\ ~ (sp1 - ESTACK <= a < sp1)).
  { intros a Ha. pose proof (op_G_low a Ha) as Hl. pose proof (op_G_frame _ _ HJ a Ha) as Hf.
    unfold kLowMemEnd, ESTACK in *. split; lia. }
  apply (HK regs2 mem2 md2 HJ2).
  + intros r Hr. exact (eq_trans (HP2 r Hr) (KR r Hr)).
  + intros j Hj.
    assert (HG1 : inG TG.G_HARNESS_B (TB_OW + 232 + Z.of_nat j))
      by (apply (op_inG_row _ _ _ _ TMAP_B_OW); unfold TB_OW, TW.SZ_OW; lia).
    destruct (OUTW _ HG1) as (O1 & O2). pose proof (op_G_low _ HG1) as Hl. unfold kLowMemEnd in Hl.
    rewrite (HK2 (TB_OW + 232 + Z.of_nat j) ltac:(lia) ltac:(lia) O2). exact (op_vm_av _ _ _ _ _ j VOW Hj).
  + intros j Hj.
    assert (HG1 : inG TG.G_HARNESS_B (TB_M + 88 + Z.of_nat j))
      by (apply (op_inG_row _ _ _ _ TMAP_B_M); unfold TB_M, TW.SZ_M; lia).
    destruct (OUTW _ HG1) as (O1 & O2). pose proof (op_G_low _ HG1) as Hl. unfold kLowMemEnd in Hl.
    rewrite (HK2 (TB_M + 88 + Z.of_nat j) ltac:(lia) ltac:(lia) O2). exact (op_vm_av _ _ _ _ _ j VM Hj).
  + intros i Hi. exact (HZ2 i Hi).
  + intros a Ha H1 H2 H3 H4. rewrite (HK2 a Ha ltac:(lia) H4). exact (KR1 a Ha H1 H2).
  + intros a Ha. exact (HG2 a (GA1 a Ha)).
Qed.

(* ------------------------------------------------------------------ *)
(* Stage K: from +0x6a4 (after the memset of c) to the key join +0xad8 *)
(* ------------------------------------------------------------------ *)

(* Atoms 32 (the kind byte at s8 = x, region k_rk), 33 (the shadow address of x, named by the alias fact k_al),
   34 (its shadow byte, region k_rs) and 35 (the address byte at s9 + 2 = x + 1, region k_ra). *)
Definition k_rk : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SOff 32 0))].
Definition k_rs : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SOff 34 0))].
Definition k_ra : YP09.region := YP09.mkRegion (Some 25%nat) 2 3 0 0 [YP09.mkChunk 2 (YP09.CVal 1 (SOff 35 0))].
Definition k_al : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 24 0) (SLit 3)) (SOff 26 0), SOff 33 0)].
Definition k_at : list (nat * afact) :=
  [(24%nat, mkAF 4096 PTRF 0); (25%nat, mkAF 4096 PTRF 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (32%nat, mkAF 0 255 0); (33%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (34%nat, mkAF 0 7 0)].
Definition ss_k3 : sstate := mkSS O_R3 sr_atoms [k_rk; k_rs; k_ra] None
  (mkFacts (k_at ++ [(35%nat, mkAF 0 255 0); (23%nat, mkAF 3 (2 ^ 26) 0); (27%nat, mkAF 2 (2 ^ 26) 0)]) [] k_al).
Definition K_Bx : sv := SOff 26 0.
Definition K_SH : list shent := [mkSHE 25 2 3].

(* The slow path's `bge a1, a0` (+0x16e0): a1 = x & 7, a0 = the shadow byte sb of x, not 0, so x mod 8 < sb < 8 and
   the branch to the report call 0x82f1c is not taken. *)
Lemma k_bge : forall E x sb b, ew E 24 = Z_to_bv 64 x -> ew E 34 = Z_to_bv 64 sb -> 0 <= x < 2 ^ 64 ->
  x mod 8 < sb < 8 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff 24 0) (SLit 7))) (sv_denot E (SOff 34 0)) = b -> b = false.
Proof.
intros E x sb b H24 H34 Hx Hsb Hb. rewrite <- Hb.
rewrite (denot_lit_U E (SAlu _ _ _)), (denot_lit_U E (SOff 34 0)).
rewrite U_and_lit by lia. rewrite !U_SOff, H24, H34, !unsigned_lit_small by lia. rewrite !Z.add_0_r.
rewrite (zcanon_id x), (zcanon_id sb) by (unfold M64; lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
set (u := x mod 8) in *.
assert (Hc : u = 0 \/ u = 1 \/ u = 2 \/ u = 3 \/ u = 4 \/ u = 5 \/ u = 6) by lia.
assert (Hs : sb = 1 \/ sb = 2 \/ sb = 3 \/ sb = 4 \/ sb = 5 \/ sb = 6 \/ sb = 7) by lia.
clearbody u.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
destruct Hs as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; first [lia | vm_compute; reflexivity].
Qed.

(* What stage K leaves at +0xad8: a1 = the kind byte or 0, a2 = the address byte or 0, s6 = 1, s7 = the bytes left,
   s8 = the cursor; every other callee-saved register and every byte kept (stage K stores nothing). *)
Definition k_post (regs : bvmap 5 word) (mem : word -> option byte) (kv av s7v s8v : Z)
    (Q : world segs -> config -> Prop) : Prop :=
  forall regs2 mem2 md2, J mem2 md2 ->
    YK11.getr regs2 11 = w64 kv -> YK11.getr regs2 12 = w64 av -> YK11.getr regs2 22 = w64 1 ->
    YK11.getr regs2 23 = w64 s7v -> YK11.getr regs2 24 = w64 s8v ->
    (forall r, acallee_saved r -> r <> 22 -> r <> 23 -> r <> 24 ->
       YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
    (forall a, 0 <= a < 2 ^ 64 -> rdv mem2 a = rdv mem a) ->
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
    SRr segs W (at_ O_KEY regs2 mem2 md2) Q.

(* Stage K when one byte was left before the op byte (s11 = 0): `beqz s11` to +0x944, a1 = a2 = s7 = 0, s6 = 1. *)
Lemma op4_k1 : forall regs mem md x (Q : world segs -> config -> Prop),
  J mem md -> YK11.getr regs 27 = w64 0 -> YK11.getr regs 24 = w64 x -> 0 <= x < 2 ^ 64 ->
  k_post regs mem 0 0 0 x Q ->
  SRr segs W (at_ O_R3 regs mem md) Q.
Proof.
intros regs mem md x Q HJ R27 R24 Hx HK.
assert (H0 : st_ok_pi segs VAL (op_E regs []) (mkSS O_R3 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - exact (conj I (conj I I)). }
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) 0 H0 R27 eq_refl) as HS. clear H0.
set (E0 := op_E regs []) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK B0 O_KEY.
{ op_awr_norm. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  pose proof (fun r => op_kr Ex regs [] (ss_regs ssx) _ r (fun m Hm => HE1 m ltac:(lia))
    (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
pmkst HS.
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 12) (w64 0) Q12 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 23) (w64 0) Q23 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 27) (w64 0) Q27 ltac:(reflexivity).
assert (Q24 : YK11.getr (ms_regs ms) (Z_to_bv 5 24) = w64 x) by (rewrite (HKR (Z_to_bv 5 24)); [exact R24 | vm_compute; reflexivity]).
apply (HK (ms_regs ms) (ms_mem ms) md1 HJ Q11 Q12 Q22 Q23 Q24).
- intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity | exact (eq_trans Q27 (eq_sym R27))].
- exact KR1.
- exact GA1.
Qed.

(* An atom plus an offset at a later valuation that agrees on the first 1024 atoms. *)
Lemma op_den : forall E E0 (n : nat) c v, (forall m, (m < 1024)%nat -> ew E m = ew E0 m) -> (n < 1024)%nat ->
  ew E0 n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E E0 n c v HE Hn H Hv Hvc. cbn [sv_denot]. rewrite (HE n Hn), H. unfold w64.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The state of stage K at +0x6a4 when two bytes were left before the op byte (s11 = 1, s7 = 2): the kind byte and
   its shadow byte, the alias fact naming the shadow address. *)
Lemma sk2_entry : forall regs mem x kb sb,
  YK11.getr regs 24 = w64 x -> YK11.getr regs 25 = w64 (x - 1) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 23 = w64 2 -> YK11.getr regs 27 = w64 1 ->
  4097 <= x -> x + 1 <= PTRF -> (x + 1 <= kLowShadowBeg \/ kHighMemBeg <= x) ->
  val_mem segs (mrestrict (w_H W) mem) x 1 kb -> 0 <= kb < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + x / 8) 1 sb -> 0 <= sb <= 7 ->
  st_ok_pi segs VAL (op_E regs [w64 kb; w64 (SHADOW_OFF + x / 8); w64 sb])
    (mkSS O_R3 (sr_set (sr_set sr_atoms (Z_to_bv 5 27) (SLit 1)) (Z_to_bv 5 23) (SLit 2)) [k_rk; k_rs] None
      (mkFacts k_at [] k_al))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem x kb sb R24 R25 R26 R23 R27 Hx1 Hx2 Happ Vkb Bkb Vsb Bsb.
pose proof asan_consts as ((C1 & C2) & _).
assert (HX8 : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold PTRF in *; lia).
set (SA := SHADOW_OFF + x / 8) in *.
set (E := op_E regs [w64 kb; w64 SA; w64 sb]).
assert (E24 : ew E 24 = w64 x) by (unfold E; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = w64 SHADOW_OFF) by (unfold E; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26).
assert (U24 : bv_unsigned (ew E 24) = x) by (rewrite E24; unfold w64; apply unsigned_lit_small; unfold PTRF in *; lia).
assert (U25 : bv_unsigned (ew E 25) = x - 1)
  by (unfold E; rewrite (op_ew regs _ 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; unfold PTRF in *; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = w64 kb) by (unfold E; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E33 : ew E 33 = w64 SA) by (unfold E; exact (op_ewx regs _ 1 ltac:(lia))).
assert (E34 : ew E 34 = w64 sb) by (unfold E; exact (op_ewx regs _ 2 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = kb) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = SA) by (rewrite E33; unfold w64; apply unsigned_lit_small; unfold SA, SHADOW_OFF in *; lia).
assert (U34 : bv_unsigned (ew E 34) = sb) by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
assert (H0 : st_ok_pi segs VAL E (mkSS O_R3 sr_atoms [k_rk; k_rs] None (mkFacts k_at [] k_al))
  (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold k_rk, k_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U24, ?U33.
    + split; [lia|]. split; [unfold PTRF in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ x 0 1 (SOff 32 0) kb); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vkb].
      cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
    + split; [unfold SA, SHADOW_OFF in *; lia|]. split; [unfold SA, SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ SA 0 1 (SOff 34 0) sb); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vsb].
      cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
  - apply pairwise_disjoint_of_extents.
    unfold k_rk, k_rs, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U24, U33. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SA, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, PTRF in *.
    repeat split; first [exact I | lia].
  - unfold k_at, k_al, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U24, U25, U26, U32, U33, U34. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SA, PTRF, SHADOW_OFF in *; lia).
    rewrite (CanKit.can_denot_shadow _ 24 26 x SHADOW_OFF E24 E26 ltac:(unfold PTRF in *; lia)
      ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF, PTRF in *; lia)).
    cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity. }
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) 1 H0 R27 eq_refl) as H1.
exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 23) 2 H1 R23 eq_refl).
Qed.

(* Stage K when two bytes were left before the op byte: the UBSan cursor test +0x6b0 (decided), the shadow test of
   the kind byte split at +0x6c4 (shadow 0: on to +0x6cc; else the slow path +0x16dc, whose `bge` is not taken), the
   kind byte, `bne s7, 2` not taken, a2 = s7 = 0. *)
Lemma op4_k2 : forall regs mem md x kb sb (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 24 = w64 x -> YK11.getr regs 25 = w64 (x - 1) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 23 = w64 2 -> YK11.getr regs 27 = w64 1 ->
  4097 <= x -> x + 1 <= PTRF -> (x + 1 <= kLowShadowBeg \/ kHighMemBeg <= x) ->
  val_mem segs (mrestrict (w_H W) mem) x 1 kb -> 0 <= kb < 256 ->
  rdv mem (SHADOW_OFF + x / 8) = Some sb -> sb = 0 \/ (x mod 8 < sb < 8) ->
  k_post regs mem kb 0 0 (x + 1) Q ->
  SRr segs W (at_ O_R3 regs mem md) Q.
Proof.
intros regs mem md x kb sb Q HJ R24 R25 R26 R23 R27 Hx1 Hx2 Happ Vkb Bkb HSB Hsbr HK.
pose proof (YE36.val_mem1_of_aview (w_H W) mem _ _ HSB) as Vsb.
assert (Bsb : 0 <= sb <= 7) by (destruct Hsbr; lia).
pose proof (sk2_entry regs mem x kb sb R24 R25 R26 R23 R27 Hx1 Hx2 Happ Vkb Bkb Vsb Bsb) as HS.
set (E0 := op_E regs [w64 kb; w64 (SHADOW_OFF + x / 8); w64 sb]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (E24 : ew E0 24 = w64 x) by (unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E0 25 = w64 (x - 1)) by (unfold E0; rewrite (op_ew regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew E0 32 = w64 kb) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E34 : ew E0 34 = w64 sb) by (unfold E0; exact (op_ewx regs _ 2 ltac:(lia))).
assert (SHOK : sh_ok segs K_Bx (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ op_awr_norm. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename ms into ms1.
(* the end of every path: +0xad8 with a1 = kb, a2 = 0, s6 = 1, s7 = 0, s8 = x + 1 *)
assert (FIN : forall regsF memF mdF,
  J memF mdF ->
  YK11.getr regsF 11 = w64 kb -> YK11.getr regsF 12 = w64 0 -> YK11.getr regsF 22 = w64 1 ->
  YK11.getr regsF 23 = w64 0 -> YK11.getr regsF 24 = w64 (x + 1) ->
  (forall r, acallee_saved r -> r <> 22 -> r <> 23 -> r <> 24 ->
     YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdv memF a = rdv (ms_mem ms1) a) ->
  (forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) memF a) ->
  SRr segs W (at_ O_KEY regsF memF mdF) Q).
{ intros regsF memF mdF HJF F11 F12 F22 F23 F24 FKR FKA FGA.
  apply (HK regsF memF mdF HJF F11 F12 F22 F23 F24 FKR).
  - intros a Ha. rewrite (FKA a Ha). exact (KR1 a Ha).
  - intros a Ha. exact (FGA a (GA1 a Ha)). }
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* the shadow byte is 0 *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O_KEY.
  { op_awr_norm. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 kb; w64 (SHADOW_OFF + x / 8); w64 sb] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 11) (w64 kb) Q11
    ltac:(rewrite (op_den _ E0 32 0 kb HE2 ltac:(lia) E32 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  op_reg HS (Z_to_bv 5 12) (w64 0) Q12 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 0) Q23 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 27) (w64 1) Q27 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 24) (w64 (x + 1)) Q24
    ltac:(rewrite (op_den _ E0 25 2 (x - 1) HE2 ltac:(lia) E25 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); f_equal; lia).
  apply (FIN (ms_regs ms) (ms_mem ms) md2 HJ Q11 Q12 Q22 Q23 Q24); [|exact KR2 | exact GA2].
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity | exact (eq_trans Q27 (eq_sym R27))].
- (* the shadow byte is not 0: the slow path *)
  rewrite branch_eq_U in Hc. rewrite (U_atom E1 34 sb ltac:(rewrite (HE1 34%nat) by lia; exact E34) ltac:(lia)) in Hc.
  rewrite (U_lit E1 0) in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hnz.
  assert (Hsb : x mod 8 < sb < 8) by (destruct Hsbr as [Hz | Hlt]; [lia | exact Hlt]). clear Hnz.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { op_awr_norm. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  rename ms into ms2.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { exfalso. pose proof (k_bge E2 x sb true ltac:(rewrite (HE2 24%nat) by lia; exact E24)
      ltac:(rewrite (HE2 34%nat) by lia; exact E34) ltac:(unfold PTRF in *; lia) Hsb Hc). discriminate. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O_KEY.
  { op_awr_norm. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
  set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in * end.
  assert (HE3 : forall m, (m < 1024)%nat -> ew E3 m = ew E0 m)
    by (intros m Hm; unfold E3; repeat rewrite ew_ewset_other by lia; apply HE2; exact Hm).
  assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha. rewrite <- (KR2 a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
  assert (GA3 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 kb; w64 (SHADOW_OFF + x / 8); w64 sb] (ss_regs ssx) _ r
      (fun m Hm => HE3 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 11) (w64 kb) Q11
    ltac:(rewrite (op_den _ E0 32 0 kb HE3 ltac:(lia) E32 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  op_reg HS (Z_to_bv 5 12) (w64 0) Q12 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 0) Q23 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 27) (w64 1) Q27 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 24) (w64 (x + 1)) Q24
    ltac:(rewrite (op_den _ E0 25 2 (x - 1) HE3 ltac:(lia) E25 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); f_equal; lia).
  apply (FIN (ms_regs ms) (ms_mem ms) md3 HJ Q11 Q12 Q22 Q23 Q24); [|exact KR3 | exact GA3].
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity | exact (eq_trans Q27 (eq_sym R27))].
Qed.

(* The state of stage K at +0x6a4 when three or more bytes were left before the op byte: the kind byte, its shadow
   byte (alias fact) and the address byte at s9 + 2; s7 = n0 in [3, 2 ^ 26], s11 = n0 - 1. *)
Lemma sk3_entry : forall regs mem x n0 kb sb ab,
  YK11.getr regs 24 = w64 x -> YK11.getr regs 25 = w64 (x - 1) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 23 = w64 n0 -> YK11.getr regs 27 = w64 (n0 - 1) -> 3 <= n0 <= 2 ^ 26 ->
  4097 <= x -> x + 2 <= PTRF -> (x + 2 <= kLowShadowBeg \/ kHighMemBeg <= x) ->
  val_mem segs (mrestrict (w_H W) mem) x 1 kb -> 0 <= kb < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + x / 8) 1 sb -> 0 <= sb <= 7 ->
  val_mem segs (mrestrict (w_H W) mem) (x + 1) 1 ab -> 0 <= ab < 256 ->
  st_ok_pi segs VAL (op_E regs [w64 kb; w64 (SHADOW_OFF + x / 8); w64 sb; w64 ab]) ss_k3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem x n0 kb sb ab R24 R25 R26 R23 R27 Hn0 Hx1 Hx2 Happ Vkb Bkb Vsb Bsb Vab Bab.
pose proof asan_consts as ((C1 & C2) & _).
assert (HX8 : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold PTRF in *; lia).
set (SA := SHADOW_OFF + x / 8) in *.
set (E := op_E regs [w64 kb; w64 SA; w64 sb; w64 ab]).
assert (E24 : ew E 24 = w64 x) by (unfold E; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = w64 SHADOW_OFF) by (unfold E; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26).
assert (U24 : bv_unsigned (ew E 24) = x) by (rewrite E24; unfold w64; apply unsigned_lit_small; unfold PTRF in *; lia).
assert (U25 : bv_unsigned (ew E 25) = x - 1)
  by (unfold E; rewrite (op_ew regs _ 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; unfold PTRF in *; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U23 : bv_unsigned (ew E 23) = n0)
  by (unfold E; rewrite (op_ew regs _ 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = n0 - 1)
  by (unfold E; rewrite (op_ew regs _ 27 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = w64 SA) by (unfold E; exact (op_ewx regs _ 1 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = kb)
  by (unfold E; rewrite (op_ewx regs _ 0 ltac:(lia)); unfold w64; apply unsigned_lit_small; cbn [nth]; lia).
assert (U33 : bv_unsigned (ew E 33) = SA) by (rewrite E33; unfold w64; apply unsigned_lit_small; unfold SA, SHADOW_OFF in *; lia).
assert (U34 : bv_unsigned (ew E 34) = sb)
  by (unfold E; rewrite (op_ewx regs _ 2 ltac:(lia)); unfold w64; apply unsigned_lit_small; cbn [nth]; lia).
assert (U35 : bv_unsigned (ew E 35) = ab)
  by (unfold E; rewrite (op_ewx regs _ 3 ltac:(lia)); unfold w64; apply unsigned_lit_small; cbn [nth]; lia).
rewrite restrict_mkst_fx. unfold ss_k3.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold k_rk, k_rs, k_ra. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U24, ?U25, ?U33.
  + split; [lia|]. split; [unfold PTRF in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ x 0 1 (SOff 32 0) kb); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vkb].
    cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
  + split; [unfold SA, SHADOW_OFF in *; lia|]. split; [unfold SA, SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ SA 0 1 (SOff 34 0) sb); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vsb].
    cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
  + split; [lia|]. split; [unfold PTRF in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (x - 1) 2 1 (SOff 35 0) ab); [| cbn; lia | cbn; lia |].
    * cbn [sv_denot]. rewrite U35, Z.add_0_r. reflexivity.
    * replace (x - 1 + 2) with (x + 1) by lia. exact Vab.
- apply pairwise_disjoint_of_extents.
  unfold k_rk, k_rs, k_ra, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U24, U25, U33. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SA, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, PTRF in *.
  repeat split; first [exact I | lia].
- unfold k_at, k_al, facts_ok. cbn [app f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U24, U25, U26, U32, U33, U34, U35, U23, U27. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SA, PTRF, SHADOW_OFF in *; lia).
  rewrite (CanKit.can_denot_shadow _ 24 26 x SHADOW_OFF E24 E26 ltac:(unfold PTRF in *; lia)
    ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF, PTRF in *; lia)).
  cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
Qed.

(* Stage K when three or more bytes were left: the kind byte as in op4_k2, `bne s7, 2` taken (+0x6d8), the UBSan
   cursor test +0xab4 and the checked load of the address byte at x + 1 (+0xac0, decided from the shadow entry K_SH),
   s7 = n0 - 3, s8 = x + 2. *)
Lemma op4_k3 : forall regs mem md x n0 kb sb ab (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 24 = w64 x -> YK11.getr regs 25 = w64 (x - 1) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 23 = w64 n0 -> YK11.getr regs 27 = w64 (n0 - 1) -> 3 <= n0 <= 2 ^ 26 ->
  4097 <= x -> x + 2 <= PTRF -> (x + 2 <= kLowShadowBeg \/ kHighMemBeg <= x) ->
  val_mem segs (mrestrict (w_H W) mem) x 1 kb -> 0 <= kb < 256 ->
  rdv mem (SHADOW_OFF + x / 8) = Some sb -> sb = 0 \/ (x mod 8 < sb < 8) ->
  val_mem segs (mrestrict (w_H W) mem) (x + 1) 1 ab -> 0 <= ab < 256 ->
  range_addressable (rdv mem) SHADOW_OFF (x + 1) 1 ->
  k_post regs mem kb ab (n0 - 3) (x + 2) Q ->
  SRr segs W (at_ O_R3 regs mem md) Q.
Proof.
intros regs mem md x n0 kb sb ab Q HJ R24 R25 R26 R23 R27 Hn0 Hx1 Hx2 Happ Vkb Bkb HSB Hsbr Vab Bab HRA HK.
pose proof (YE36.val_mem1_of_aview (w_H W) mem _ _ HSB) as Vsb.
assert (Bsb : 0 <= sb <= 7) by (destruct Hsbr; lia).
pose proof (sk3_entry regs mem x n0 kb sb ab R24 R25 R26 R23 R27 Hn0 Hx1 Hx2 Happ Vkb Bkb Vsb Bsb Vab Bab) as HS.
set (E0 := op_E regs [w64 kb; w64 (SHADOW_OFF + x / 8); w64 sb; w64 ab]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (E23 : ew E0 23 = w64 n0) by (unfold E0; rewrite (op_ew regs _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E0 24 = w64 x) by (unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E0 25 = w64 (x - 1)) by (unfold E0; rewrite (op_ew regs _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E0 26 = w64 SHADOW_OFF) by (unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E0 32 = w64 kb) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E34 : ew E0 34 = w64 sb) by (unfold E0; exact (op_ewx regs _ 2 ltac:(lia))).
assert (E35 : ew E0 35 = w64 ab) by (unfold E0; exact (op_ewx regs _ 3 ltac:(lia))).
assert (SHOK : sh_ok segs K_Bx K_SH E0 (mrestrict (w_H W) mem)).
{ unfold K_SH. repeat apply Forall_cons; try apply Forall_nil.
  apply (shent_ok_of_range segs (w_H W) mem E0 K_Bx 25%nat (x + 1) 1 (x - 1) 2 3 HRA).
  - unfold K_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E25 | unfold PTRF in *; lia].
  - lia.
  - lia.
  - intros y Hy. cbn [Z.min Z.max] in Hy. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, PTRF in *. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ op_awr_norm. op_awr_ro. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename ms into ms1.
assert (FIN : forall regsF memF mdF,
  J memF mdF ->
  YK11.getr regsF 11 = w64 kb -> YK11.getr regsF 12 = w64 ab -> YK11.getr regsF 22 = w64 1 ->
  YK11.getr regsF 23 = w64 (n0 - 3) -> YK11.getr regsF 24 = w64 (x + 2) ->
  (forall r, acallee_saved r -> r <> 22 -> r <> 23 -> r <> 24 ->
     YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdv memF a = rdv (ms_mem ms1) a) ->
  (forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) memF a) ->
  SRr segs W (at_ O_KEY regsF memF mdF) Q).
{ intros regsF memF mdF HJF F11 F12 F22 F23 F24 FKR FKA FGA.
  apply (HK regsF memF mdF HJF F11 F12 F22 F23 F24 FKR).
  - intros a Ha. rewrite (FKA a Ha). exact (KR1 a Ha).
  - intros a Ha. exact (FGA a (GA1 a Ha)). }
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* the shadow byte of x is 0 *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O_KEY.
  { op_awr_norm. op_awr_ro. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 kb; w64 (SHADOW_OFF + x / 8); w64 sb; w64 ab] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 11) (w64 kb) Q11
    ltac:(rewrite (op_den _ E0 32 0 kb HE2 ltac:(lia) E32 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  op_reg HS (Z_to_bv 5 12) (w64 ab) Q12
    ltac:(rewrite (op_den _ E0 35 0 ab HE2 ltac:(lia) E35 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 (n0 - 3)) Q23
    ltac:(rewrite (op_den _ E0 23 (-3) n0 HE2 ltac:(lia) E23 ltac:(lia) ltac:(lia)); f_equal; lia).
  op_reg HS (Z_to_bv 5 24) (w64 (x + 2)) Q24
    ltac:(rewrite (op_den _ E0 25 3 (x - 1) HE2 ltac:(lia) E25 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); f_equal; lia).
  apply (FIN (ms_regs ms) (ms_mem ms) md2 HJ Q11 Q12 Q22 Q23 Q24); [|exact KR2 | exact GA2].
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity].
- (* the shadow byte of x is not 0: the slow path *)
  rewrite branch_eq_U in Hc. rewrite (U_atom E1 34 sb ltac:(rewrite (HE1 34%nat) by lia; exact E34) ltac:(lia)) in Hc.
  rewrite (U_lit E1 0) in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hnz.
  assert (Hsb : x mod 8 < sb < 8) by (destruct Hsbr as [Hz | Hlt]; [lia | exact Hlt]). clear Hnz.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { op_awr_norm. op_awr_ro. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  rename ms into ms2.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { exfalso. pose proof (k_bge E2 x sb true ltac:(rewrite (HE2 24%nat) by lia; exact E24)
      ltac:(rewrite (HE2 34%nat) by lia; exact E34) ltac:(unfold PTRF in *; lia) Hsb Hc). discriminate. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O_KEY.
  { op_awr_norm. op_awr_ro. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
  set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in * end.
  assert (HE3 : forall m, (m < 1024)%nat -> ew E3 m = ew E0 m)
    by (intros m Hm; unfold E3; repeat rewrite ew_ewset_other by lia; apply HE2; exact Hm).
  assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha. rewrite <- (KR2 a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi y Hiw Hy. cbv beta. op_win Hiw Hy ltac:(lia). }
  assert (GA3 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 kb; w64 (SHADOW_OFF + x / 8); w64 sb; w64 ab] (ss_regs ssx) _ r
      (fun m Hm => HE3 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 11) (w64 kb) Q11
    ltac:(rewrite (op_den _ E0 32 0 kb HE3 ltac:(lia) E32 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  op_reg HS (Z_to_bv 5 12) (w64 ab) Q12
    ltac:(rewrite (op_den _ E0 35 0 ab HE3 ltac:(lia) E35 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 (n0 - 3)) Q23
    ltac:(rewrite (op_den _ E0 23 (-3) n0 HE3 ltac:(lia) E23 ltac:(lia) ltac:(lia)); f_equal; lia).
  op_reg HS (Z_to_bv 5 24) (w64 (x + 2)) Q24
    ltac:(rewrite (op_den _ E0 25 3 (x - 1) HE3 ltac:(lia) E25 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); f_equal; lia).
  apply (FIN (ms_regs ms) (ms_mem ms) md3 HJ Q11 Q12 Q22 Q23 Q24); [|exact KR3 | exact GA3].
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* Stage D: from the key join +0xad8 to SUBR (+0x12bc) or SUBT (+0xfa4) *)
(* ------------------------------------------------------------------ *)

(* The regions: c's byte 25 (the display byte) and bytes 28 .. 31 (the key word) at s4 (atom 20, written), the spill
   104(s1) (g_raw's page), g_raw (atom 32), the spill 144(s1) (c), the spill 24(s1) (written on the tagged path); and
   the window of the k input bytes after the key at s8 (atom 24): the display byte (atom 33), the length word's two
   bytes (atoms 34, 35). *)
Definition d_rc25 : YP09.region := YP09.mkRegion (Some 20%nat) 25 26 25 26 [].
Definition d_rc28 : YP09.region := YP09.mkRegion (Some 20%nat) 28 32 28 32 [].
Definition d_r104 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 104 112 0 0 [YP09.mkChunk 104 (YP09.CVal 8 (SLit PG_RAW))].
Definition d_rg : YP09.region :=
  YP09.mkRegion None TB_g_raw (TB_g_raw + 4) 0 0 [YP09.mkChunk TB_g_raw (YP09.CVal 4 (SOff 32 0))].
Definition d_r144 : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (YP09.CVal 8 (SOff 20 0))].
Definition d_r24 : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition d_base : smem := [d_rc25; d_rc28; d_r104; d_rg; d_r144; d_r24].
Definition d_ch : list YP09.chunk :=
  [YP09.mkChunk 0 (YP09.CVal 1 (SOff 33 0)); YP09.mkChunk 1 (YP09.CVal 1 (SOff 34 0));
   YP09.mkChunk 2 (YP09.CVal 1 (SOff 35 0))].
Definition d_win (k : nat) : YP09.region := YP09.mkRegion (Some 24%nat) 0 (Z.of_nat k) 0 0 (firstn k d_ch).
Definition d_at : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF 4096 PTRF 5); (11%nat, mkAF 0 255 0); (12%nat, mkAF 0 255 0);
   (24%nat, mkAF 4096 PTRF 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 32 - 1) 0);
   (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)].
Definition ss_d0 : sstate := mkSS O_KEY sr_atoms d_base None (mkFacts d_at [] []).
Definition D_SH (k : nat) : list shent := [mkSHE 24 0 (Z.of_nat k); mkSHE 20 25 32].

(* Stage D's base state at +0xad8. *)
Lemma sd_entry : forall regs mem x g kv av b0 b1 b2,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 (F + 32) -> YK11.getr regs 11 = w64 kv ->
  YK11.getr regs 12 = w64 av -> YK11.getr regs 24 = w64 x -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  0 <= kv < 256 -> 0 <= av < 256 -> 4096 <= x <= PTRF ->
  rdword (rdv mem) (sp1 + 104) = Some PG_RAW -> rdword (rdv mem) (sp1 + 144) = Some (F + 32) ->
  val_mem segs (mrestrict (w_H W) mem) TB_g_raw 4 g -> 0 <= g < 2 ^ 32 ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  (forall a, F + 57 <= a < F + 64 -> apresent (w_H W) mem a) ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  st_ok_pi segs VAL (op_E regs [w64 g; w64 b0; w64 b1; w64 b2]) ss_d0
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_KEY)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem x g kv av b0 b1 b2 R9 R20 R11 R12 R24 R26 Hkv Hav Hx H104 H144 HGV HG Psp Pc Hb0 Hb1 Hb2.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (MF : (F + 32) mod 32 = 0).
{ rewrite DF. replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by ring. apply Z.mod_mul. lia. }
set (E := op_E regs [w64 g; w64 b0; w64 b1; w64 b2]).
assert (UR : forall n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v)
  by (intros n r v Hn Hr Hv; unfold E; rewrite (op_ew regs _ n r Hn), Hr; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 20%nat 20%bv (F + 32) eq_refl R20 ltac:(lia)) as U20.
pose proof (UR 11%nat 11%bv kv eq_refl R11 ltac:(lia)) as U11.
pose proof (UR 12%nat 12%bv av eq_refl R12 ltac:(lia)) as U12.
pose proof (UR 24%nat 24%bv x eq_refl R24 ltac:(unfold PTRF in *; lia)) as U24.
pose proof (UR 26%nat 26%bv SHADOW_OFF eq_refl R26 ltac:(unfold SHADOW_OFF; lia)) as U26.
assert (EX : forall j v, (j < 4)%nat -> nth j [w64 g; w64 b0; w64 b1; w64 b2] (Z_to_bv 64 0) = w64 v ->
  0 <= v < 2 ^ 64 -> ew E (32 + j) = w64 v /\ bv_unsigned (ew E (32 + j)) = v).
{ intros j v Hj Hv Hb. unfold E. rewrite (op_ewx regs _ j ltac:(lia)), Hv. split; [reflexivity|].
  unfold w64. apply unsigned_lit_small. lia. }
destruct (EX 0%nat g ltac:(lia) eq_refl ltac:(lia)) as (E32 & U32).
destruct (EX 1%nat b0 ltac:(lia) eq_refl ltac:(lia)) as (_ & U33).
destruct (EX 2%nat b1 ltac:(lia) eq_refl ltac:(lia)) as (_ & U34).
destruct (EX 3%nat b2 ltac:(lia) eq_refl ltac:(lia)) as (_ & U35).
cbn [Nat.add] in E32, U32, U33, U34, U35.
assert (E20 : ew E 20 = w64 (F + 32)) by (unfold E; rewrite (op_ew regs _ 20 20%bv eq_refl); exact R20).
rewrite restrict_mkst_fx. unfold ss_d0, d_base, d_rc25, d_rc28, d_r104, d_rg, d_r144, d_r24.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9, ?U20.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Pc. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Pc. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 104 8 (SLit PG_RAW) PG_RAW); [reflexivity | unfold PG_RAW; cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword segs _ _ _ _ H104).
  + split; [unfold TB_g_raw; lia|]. split; [unfold TB_g_raw; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 TB_g_raw 4 (SOff 32 0) g); [| cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HGV].
    cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 144 8 (SOff 20 0) (F + 32)); [| cbn; lia | cbn; lia |].
    * cbn [sv_denot]. rewrite U20, Z.add_0_r. reflexivity.
    * exact (val_mem_of_rdword segs _ _ _ _ H144).
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Psp. lia.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TB_g_raw in *. repeat split; first [exact I | lia].
- unfold d_at, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U20, U11, U12, U24, U26, U32, U33, U34, U35.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold PTRF, SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* What stage D leaves: SUBR when g <> 0 (a1 = the length word wv, s8 / s7 the cursor after it, s4 = c, s6 = 1) or
   SUBT when g = 0 (s9 / s6 the cursor after the display byte, s4 = 1, 24(s1) = s5); c + 25 = the display bit, c + 28
   = the key, every other byte but 24(s1) .. 31(s1) kept, every other callee-saved register kept. *)
Definition d_post (regs : bvmap 5 word) (mem : word -> option byte) (g disp key wv curR nR curT nT : Z)
    (Q : world segs -> config -> Prop) : Prop :=
  forall regs2 mem2 md2 pc, J mem2 md2 ->
    ((pc = LO_SUBR /\ g <> 0 /\ YK11.getr regs2 11 = w64 wv /\ YK11.getr regs2 24 = w64 curR /\
      YK11.getr regs2 23 = w64 nR /\ YK11.getr regs2 20 = w64 (F + 32) /\ YK11.getr regs2 22 = w64 1) \/
     (pc = LO_SUBT /\ g = 0 /\ YK11.getr regs2 25 = w64 curT /\ YK11.getr regs2 22 = w64 nT /\
      YK11.getr regs2 20 = w64 1 /\ rdword (rdv mem2) (sp1 + 24) = Some (bv_unsigned (YK11.getr regs 21)))) ->
    (forall r, acallee_saved r -> r <> 20 -> r <> 22 -> r <> 23 -> r <> 24 -> r <> 25 ->
       YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
    rdv mem2 (F + 57) = Some disp ->
    (forall j, (j < 4)%nat -> rdv mem2 (F + 60 + Z.of_nat j) = Some (YO0f.le_byte key 4 j)) ->
    (forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 24 <= a < sp1 + 32) ->
       rdv mem2 a = rdv mem a) ->
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
    SRr segs W (at_ pc regs2 mem2 md2) Q.

(* The write rights of a stage-D run, region by region: c's bytes 25 and 28 .. 31 in the own frame, the spills 104,
   g_raw and 144 read only, the stack spill 24(s1); then the input window, read only (Un20 / Un9: atoms 20 and 9 at
   the run's valuation). *)
Ltac d_own Un20 :=
  eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Un20 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite HFA; change (fs_frame_bytes LF_CID) with 256; lia |].
Ltac d_stk Un9 :=
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Un9 in Ha;
    left; split; [unfold awr_byte; left; unfold ESTACK in *; lia | lia] |].
Ltac d_awr Un20 Un9 :=
  op_awr_norm; d_own Un20; d_own Un20; op_awr_ro; op_awr_ro; op_awr_ro; d_stk Un9;
  repeat op_awr_ro; apply awr_ok_x_nil.

(* c's display byte and key word at a state of stage D: the chunks of the two c regions. *)
Lemma d_ck : forall E (H : word -> bool) m lo1 hi1 wlo1 whi1 cs1 lo2 hi2 wlo2 whi2 cs2 e kv av,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some 20%nat) lo1 hi1 wlo1 whi1 cs1) ->
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some 20%nat) lo2 hi2 wlo2 whi2 cs2) ->
  In (YP09.mkChunk 25 (YP09.CVal 1 e)) cs1 -> In (YP09.mkChunk 28 (YP09.CVal 4 kexprC)) cs2 ->
  bv_unsigned (ew E 20) = F + 32 -> U E (SOff 11 0) = kv -> U E (SOff 12 0) = av -> 0 <= kv < 256 -> 0 <= av < 256 ->
  aview segs H m (F + 57) = Some (U E e mod 256) /\
  (forall j, (j < 4)%nat -> aview segs H m (F + 60 + Z.of_nat j) = Some (YO0f.le_byte (DSpec.KEY (kv mod 9 + 1) av) 4 j)).
Proof.
intros E H m lo1 hi1 wlo1 whi1 cs1 lo2 hi2 wlo2 whi2 cs2 e kv av R1 R2 I1 I2 U20e Uk Ua Hkv Hav.
split.
- pose proof (op_chunk_val E H m _ _ _ _ _ _ 25 1 e R1 I1 ltac:(lia)) as V. cbn [base_val] in V. rewrite U20e in V.
  replace (F + 32 + 25) with (F + 57) in V by lia. change (N.to_nat 1) with 1%nat in V.
  change (bv_unsigned (sv_denot E e)) with (U E e) in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
  apply (TransportGNoticeB.aview_of_val_mem1 H m _ _ V). apply Z.mod_pos_bound. lia.
- intros j Hj. pose proof (op_chunk_val E H m _ _ _ _ _ _ 28 4 kexprC R2 I2 ltac:(lia)) as V.
  cbn [base_val] in V. rewrite U20e in V.
  change (bv_unsigned (sv_denot E kexprC)) with (U E kexprC) in V.
  rewrite (kexprC_U E kv av Uk Ua Hkv Hav) in V.
  destruct (op_key_val kv av Hkv Hav) as (_ & BK).
  change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V. rewrite Z.mod_small in V by exact BK.
  change (N.to_nat 4) with 4%nat in V.
  replace (F + 60 + Z.of_nat j) with (F + 32 + 28 + Z.of_nat j) by lia. exact (op_vm_av _ _ _ _ _ j V Hj).
Qed.

(* Stage D when no byte is left after the key bytes (s7 = 0): the key at c + 28, `beqz s7` to +0xb90, g_raw, c + 25
   := 0, `beqz g_raw`: SUBT (+0xf94: 24(s1) := s5, s4 = 1, s6 = 0, s9 = s8) or SUBR (+0xba0, +0x12b4: a1 = 0). *)
Lemma op4_d0 : forall regs mem md x g kv av (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 (F + 32) -> YK11.getr regs 11 = w64 kv ->
  YK11.getr regs 12 = w64 av -> YK11.getr regs 24 = w64 x -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 0 ->
  0 <= kv < 256 -> 0 <= av < 256 -> 4096 <= x <= PTRF ->
  rdword (rdv mem) (sp1 + 104) = Some PG_RAW -> rdword (rdv mem) (sp1 + 144) = Some (F + 32) ->
  val_mem segs (mrestrict (w_H W) mem) TB_g_raw 4 g -> 0 <= g < 2 ^ 32 ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  (forall a, F + 57 <= a < F + 64 -> apresent (w_H W) mem a) ->
  d_post regs mem g 0 (DSpec.KEY (kv mod 9 + 1) av) 0 x 0 x 0 Q ->
  SRr segs W (at_ O_KEY regs mem md) Q.
Proof.
intros regs mem md x g kv av Q HJ R9 R20 R11 R12 R24 R26 R22 R23 Hkv Hav Hx H104 H144 HGV Hg32 Psp Pc HK.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (sd_entry regs mem x g kv av 0 0 0 R9 R20 R11 R12 R24 R26 Hkv Hav Hx H104 H144 HGV Hg32 Psp Pc
  ltac:(lia) ltac:(lia) ltac:(lia)) as H0.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 22) 1 H0 R22 eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 23) 0 H1 R23 eq_refl) as HS. clear H0 H1.
set (E0 := op_E regs [w64 g; w64 0; w64 0; w64 0]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (E9 : ew E0 9 = w64 sp1) by (unfold E0; rewrite (op_ew regs _ 9 9%bv eq_refl); exact R9).
assert (E20 : ew E0 20 = w64 (F + 32)) by (unfold E0; rewrite (op_ew regs _ 20 20%bv eq_refl); exact R20).
assert (E11 : ew E0 11 = w64 kv) by (unfold E0; rewrite (op_ew regs _ 11 11%bv eq_refl); exact R11).
assert (E12 : ew E0 12 = w64 av) by (unfold E0; rewrite (op_ew regs _ 12 12%bv eq_refl); exact R12).
assert (E24 : ew E0 24 = w64 x) by (unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24).
assert (E21 : ew E0 21 = YK11.getr regs 21) by (unfold E0; exact (op_ew regs _ 21 21%bv eq_refl)).
assert (E32 : ew E0 32 = w64 g) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (U9 : bv_unsigned (ew E0 9) = sp1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E0 20) = F + 32) by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK B0.
{ d_awr U20 U9. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U20' : bv_unsigned (ew E1 20) = F + 32) by (rewrite (HE1 20%nat) by lia; exact U20).
assert (U9' : bv_unsigned (ew E1 9) = sp1) by (rewrite (HE1 9%nat) by lia; exact U9).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 24 <= a < sp1 + 32) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
    [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
  intros b wlo whi y Hiw Hy. cbv beta.
  op_win Hiw Hy ltac:(rewrite ?U20', ?U9' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename ms into ms1.
assert (U32' : U E1 (SOff 32 0) = g)
  by (apply U_atom; [rewrite (HE1 32%nat) by lia; exact E32 | lia]).
psrr_branch_tok RUN BR HS SHOK B0.
- (* g_raw = 0: SUBT *)
  destruct (op_swrap_z g Hg32) as ((S1 & _) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small g) in Hc by lia.
  apply Z.eqb_eq in Hc. apply S1 in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK B0 LO_SUBT.
  { d_awr U20' U9'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U20'' : bv_unsigned (ew E2 20) = F + 32) by (rewrite (HE2 20%nat) by lia; exact U20).
  assert (U9'' : bv_unsigned (ew E2 9) = sp1) by (rewrite (HE2 9%nat) by lia; exact U9).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) ->
    ~ (sp1 + 24 <= a < sp1 + 32) -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1 H2 H3.
    apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
      [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
    intros b wlo whi y Hiw Hy. cbv beta.
    op_win Hiw Hy ltac:(rewrite ?U20'', ?U9'' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  destruct (d_ck E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ (SLit 0) kv av RG0 RG1
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    U20'' (U_atom E2 11 kv ltac:(rewrite (HE2 11%nat) by lia; exact E11) ltac:(lia))
    (U_atom E2 12 av ltac:(rewrite (HE2 12%nat) by lia; exact E12) ltac:(lia)) Hkv Hav) as (VD & VK).
  rewrite (U_lit E2 0) in VD by lia. change (0 mod 256) with 0 in VD.
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 5 _ HS eq_refl) as RG5. cbn [ms_mem restrict] in RG5.
  pose proof (op_chunk_val E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ 24 8 (SOff 21 0) RG5
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VS.
  cbn [base_val] in VS. rewrite U9'' in VS.
  assert (E21' : ew E2 21 = YK11.getr regs 21) by exact (eq_trans (HE2 21%nat ltac:(lia)) E21).
  replace (bv_unsigned (sv_denot E2 (SOff 21 0)) mod 2 ^ (8 * Z.of_N 8)) with (bv_unsigned (YK11.getr regs 21)) in VS.
  2: { cbn [sv_denot]. rewrite E21'.
       rewrite Z.add_0_r, Z_to_bv_bv_unsigned. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 21)) as Hr.
       change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
       rewrite Z.mod_small by lia. reflexivity. }
  change (N.to_nat 8) with 8%nat in VS.
  clear HF HFr HG RG5 RG0 RG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 g; w64 0; w64 0; w64 0] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 25) (w64 x) Q25
    ltac:(rewrite (op_den _ E0 24 0 x HE2 ltac:(lia) E24 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)), Z.add_0_r; reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 0) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 20) (w64 1) Q20 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 0) Q23 ltac:(reflexivity).
  apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBT HJ).
  + right. split; [reflexivity|]. split; [exact Hc|]. split; [exact Q25|]. split; [exact Q22|].
    split; [exact Q20|].
    apply YF0x.val_mem_rdword; [|exact VS]. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 21)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H20 H22 H23 H24 H25;
      first [exfalso; lia | apply HKR; vm_compute; reflexivity].
  + exact VD.
  + exact VK.
  + intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 H2 H3). exact (KR1 a Ha H1 H2 H3).
  + intros a Ha. exact (GA2 a (GA1 a Ha)).
- (* g_raw <> 0: SUBR *)
  destruct (op_swrap_z g Hg32) as ((_ & S1) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small g) in Hc by lia.
  apply Z.eqb_neq in Hc.
  assert (Hg0 : g <> 0) by (intros Eg; apply Hc; exact (S1 Eg)). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK B0 LO_SUBR.
  { d_awr U20' U9'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U20'' : bv_unsigned (ew E2 20) = F + 32) by (rewrite (HE2 20%nat) by lia; exact U20).
  assert (U9'' : bv_unsigned (ew E2 9) = sp1) by (rewrite (HE2 9%nat) by lia; exact U9).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) ->
    ~ (sp1 + 24 <= a < sp1 + 32) -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1 H2 H3.
    apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
      [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
    intros b wlo whi y Hiw Hy. cbv beta.
    op_win Hiw Hy ltac:(rewrite ?U20'', ?U9'' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  destruct (d_ck E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ (SLit 0) kv av RG0 RG1
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    U20'' (U_atom E2 11 kv ltac:(rewrite (HE2 11%nat) by lia; exact E11) ltac:(lia))
    (U_atom E2 12 av ltac:(rewrite (HE2 12%nat) by lia; exact E12) ltac:(lia)) Hkv Hav) as (VD & VK).
  rewrite (U_lit E2 0) in VD by lia. change (0 mod 256) with 0 in VD.
  clear HF HFr HG RG0 RG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 g; w64 0; w64 0; w64 0] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 0) Q23 ltac:(reflexivity).
  assert (Q24 : YK11.getr (ms_regs ms) (Z_to_bv 5 24) = w64 x)
    by (rewrite (HKR (Z_to_bv 5 24)); [exact R24 | vm_compute; reflexivity]).
  assert (Q20 : YK11.getr (ms_regs ms) (Z_to_bv 5 20) = w64 (F + 32))
    by (rewrite (HKR (Z_to_bv 5 20)); [exact R20 | vm_compute; reflexivity]).
  apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBR HJ).
  + left. split; [reflexivity|]. split; [exact Hg0|]. split; [exact Q11|]. split; [exact Q24|].
    split; [exact Q23|]. split; [exact Q20 | exact Q22].
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H20 H22 H23 H24 H25;
      first [exfalso; lia | apply HKR; vm_compute; reflexivity].
  + exact VD.
  + exact VK.
  + intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 H2 H3). exact (KR1 a Ha H1 H2 H3).
  + intros a Ha. exact (GA2 a (GA1 a Ha)).
Qed.

(* The write rights of a run of stage D with the input window first (read only). *)
Ltac d_awrw Un20 Un9 :=
  op_awr_norm; op_awr_ro; d_own Un20; d_own Un20; op_awr_ro; op_awr_ro; op_awr_ro; d_stk Un9; apply awr_ok_x_nil.

(* The display bit the `andi` at +0xb34 leaves, at a valuation that holds the display byte at atom 33. *)
Lemma d_disp : forall E db, ew E 33 = w64 db -> 0 <= db < 256 ->
  U E (SAlu ALU_AND (SOff 33 0) (SLit 1)) mod 256 = Z.land db 1.
Proof.
intros E db H33 Hdb. rewrite U_and_lit by lia. rewrite (U_atom E 33 db H33 ltac:(lia)).
assert (E1 : Z.land db 1 = db mod 2 ^ 1) by exact (Z.land_ones db 1 ltac:(lia)).
rewrite E1. pose proof (Z.mod_pos_bound db (2 ^ 1) ltac:(lia)). apply Z.mod_small. change (2 ^ 1) with 2 in *. lia.
Qed.

(* Stage D when one byte is left after the key bytes (s7 = 1): the display byte (the checked load +0xb20, decided
   from the shadow entry of the window), g_raw, c + 25 := display & 1, s6 = 0, `beqz g_raw`: SUBT (+0xd14) or SUBR
   (`beqz s6` to +0xf78, +0x12b4: a1 = 0, s8 = s9, s4 = c). *)
Lemma op4_d1 : forall regs mem md x g kv av db (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 (F + 32) -> YK11.getr regs 11 = w64 kv ->
  YK11.getr regs 12 = w64 av -> YK11.getr regs 24 = w64 x -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 1 ->
  0 <= kv < 256 -> 0 <= av < 256 -> 4096 <= x -> x + 1 <= PTRF ->
  (x + 1 <= kLowShadowBeg \/ kHighMemBeg <= x) ->
  (x + 1 <= F \/ F + 256 <= x) -> x + 1 <= sp1 -> (x + 1 <= TB_g_raw \/ TB_g_raw + 4 <= x) ->
  rdword (rdv mem) (sp1 + 104) = Some PG_RAW -> rdword (rdv mem) (sp1 + 144) = Some (F + 32) ->
  val_mem segs (mrestrict (w_H W) mem) TB_g_raw 4 g -> 0 <= g < 2 ^ 32 ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  (forall a, F + 57 <= a < F + 64 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 8 -> rdv mem (SHF + i) = Some 0) ->
  val_mem segs (mrestrict (w_H W) mem) x 1 db -> 0 <= db < 256 ->
  range_addressable (rdv mem) SHADOW_OFF x 1 ->
  d_post regs mem g (Z.land db 1) (DSpec.KEY (kv mod 9 + 1) av) 0 (x + 1) 0 (x + 1) 0 Q ->
  SRr segs W (at_ O_KEY regs mem md) Q.
Proof.
intros regs mem md x g kv av db Q HJ R9 R20 R11 R12 R24 R26 R22 R23 Hkv Hav Hx1 Hx2 Happ Hfr Hsp Hgr H104 H144 HGV
  Hg32 Psp Pc HZS Vdb Hdb HRA HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
destruct (op_frame_pres mem md HJ) as (_ & _ & HFapp).
pose proof (sd_entry regs mem x g kv av db 0 0 R9 R20 R11 R12 R24 R26 Hkv Hav ltac:(lia) H104 H144 HGV Hg32 Psp Pc
  Hdb ltac:(lia) ltac:(lia)) as H0.
set (E0 := op_E regs [w64 g; w64 db; w64 0; w64 0]) in H0.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (E9 : ew E0 9 = w64 sp1) by (unfold E0; rewrite (op_ew regs _ 9 9%bv eq_refl); exact R9).
assert (E20 : ew E0 20 = w64 (F + 32)) by (unfold E0; rewrite (op_ew regs _ 20 20%bv eq_refl); exact R20).
assert (E11 : ew E0 11 = w64 kv) by (unfold E0; rewrite (op_ew regs _ 11 11%bv eq_refl); exact R11).
assert (E12 : ew E0 12 = w64 av) by (unfold E0; rewrite (op_ew regs _ 12 12%bv eq_refl); exact R12).
assert (E24 : ew E0 24 = w64 x) by (unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E0 26 = w64 SHADOW_OFF) by (unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26).
assert (E21 : ew E0 21 = YK11.getr regs 21) by (unfold E0; exact (op_ew regs _ 21 21%bv eq_refl)).
assert (E32 : ew E0 32 = w64 g) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E33 : ew E0 33 = w64 db) by (unfold E0; exact (op_ewx regs _ 1 ltac:(lia))).
assert (U9 : bv_unsigned (ew E0 9) = sp1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E0 20) = F + 32) by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E0 24) = x) by (rewrite E24; unfold w64; apply unsigned_lit_small; unfold PTRF in *; lia).
assert (Hwin : region_ok segs E0 (mrestrict (w_H W) mem) (d_win 1)).
{ unfold d_win, region_ok.
  cbn [firstn d_ch YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_nat].
  rewrite U24. split; [lia|]. split; [unfold PTRF in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E0 _ x 0 1 (SOff 33 0) db); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vdb].
  cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hdis : all_disjoint E0 (d_win 1) (ss_mem ss_d0)).
{ apply all_disjoint_of_extents.
  unfold ss_d0, d_base, d_win, d_rc25, d_rc28, d_r104, d_rg, d_r144, d_r24, extent_of_region.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_nat]. rewrite U24, U9, U20.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold TB_g_raw in *. repeat split; lia. }
pose proof (st_ok_pi_add_region _ _ _ (d_win 1) H0 eq_refl Hwin Hdis) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 22) 1 H1 R22 eq_refl) as H2.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 23) 1 H2 R23 eq_refl) as HS. clear H0 H1 H2.
assert (SHOK : sh_ok segs K_Bx (D_SH 1) E0 (mrestrict (w_H W) mem)).
{ unfold D_SH. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range segs (w_H W) mem E0 K_Bx 24%nat x 1 x 0 (Z.of_nat 1) HRA).
    + unfold K_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E24 | unfold PTRF in *; lia].
    + lia.
    + cbn. lia.
    + intros y Hy. cbn [Z.min Z.max Z.of_nat] in Hy. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, PTRF in *. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E0 K_Bx 20%nat (F + 57) 7 (F + 32) 25 32).
    + apply (TGNA.frame_ra_zero _ F (F + 57) 7 7 8); [lia | exact F8m | lia | lia |].
      intros i Hi. exact (HZS i ltac:(lia)).
    + unfold K_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E20 | lia].
    + lia.
    + lia.
    + intros y Hy. cbn [Z.min Z.max] in Hy. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
      unfold SHADOW_OFF. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ d_awrw U20 U9. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U20' : bv_unsigned (ew E1 20) = F + 32) by (rewrite (HE1 20%nat) by lia; exact U20).
assert (U9' : bv_unsigned (ew E1 9) = sp1) by (rewrite (HE1 9%nat) by lia; exact U9).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 24 <= a < sp1 + 32) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
    [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
  intros b wlo whi y Hiw Hy. cbv beta.
  op_win Hiw Hy ltac:(rewrite ?U20', ?U9' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename ms into ms1.
assert (U32' : U E1 (SOff 32 0) = g)
  by (apply U_atom; [rewrite (HE1 32%nat) by lia; exact E32 | lia]).
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* g_raw = 0: SUBT *)
  destruct (op_swrap_z g Hg32) as ((S1 & _) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small g) in Hc by lia.
  apply Z.eqb_eq in Hc. apply S1 in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SUBT.
  { d_awrw U20' U9'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U20'' : bv_unsigned (ew E2 20) = F + 32) by (rewrite (HE2 20%nat) by lia; exact U20).
  assert (U9'' : bv_unsigned (ew E2 9) = sp1) by (rewrite (HE2 9%nat) by lia; exact U9).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) ->
    ~ (sp1 + 24 <= a < sp1 + 32) -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1 H2 H3.
    apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
      [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
    intros b wlo whi y Hiw Hy. cbv beta.
    op_win Hiw Hy ltac:(rewrite ?U20'', ?U9'' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  destruct (d_ck E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ (SAlu ALU_AND (SOff 33 0) (SLit 1)) kv av RG1 RG2
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    U20'' (U_atom E2 11 kv ltac:(rewrite (HE2 11%nat) by lia; exact E11) ltac:(lia))
    (U_atom E2 12 av ltac:(rewrite (HE2 12%nat) by lia; exact E12) ltac:(lia)) Hkv Hav) as (VD & VK).
  rewrite (d_disp E2 db ltac:(rewrite (HE2 33%nat) by lia; exact E33) Hdb) in VD.
  pose proof (st_ok_pi_region_nth _ _ _ 6 _ HS eq_refl) as RG6. cbn [ms_mem restrict] in RG6.
  pose proof (op_chunk_val E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ 24 8 (SOff 21 0) RG6
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VS.
  cbn [base_val] in VS. rewrite U9'' in VS.
  assert (E21' : ew E2 21 = YK11.getr regs 21) by exact (eq_trans (HE2 21%nat ltac:(lia)) E21).
  replace (bv_unsigned (sv_denot E2 (SOff 21 0)) mod 2 ^ (8 * Z.of_N 8)) with (bv_unsigned (YK11.getr regs 21)) in VS.
  2: { cbn [sv_denot]. rewrite E21'.
       rewrite Z.add_0_r, Z_to_bv_bv_unsigned. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 21)) as Hr.
       change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
       rewrite Z.mod_small by lia. reflexivity. }
  change (N.to_nat 8) with 8%nat in VS.
  clear HF HFr HG RG6 RG1 RG2.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 g; w64 db; w64 0; w64 0] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 25) (w64 (x + 1)) Q25
    ltac:(rewrite (op_den _ E0 24 1 x HE2 ltac:(lia) E24 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 0) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 20) (w64 1) Q20 ltac:(reflexivity).
  apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBT HJ).
  + right. split; [reflexivity|]. split; [exact Hc|]. split; [exact Q25|]. split; [exact Q22|].
    split; [exact Q20|].
    apply YF0x.val_mem_rdword; [|exact VS]. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 21)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H20 H22 H23 H24 H25;
      first [exfalso; lia | apply HKR; vm_compute; reflexivity].
  + exact VD.
  + exact VK.
  + intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 H2 H3). exact (KR1 a Ha H1 H2 H3).
  + intros a Ha. exact (GA2 a (GA1 a Ha)).
- (* g_raw <> 0: SUBR *)
  destruct (op_swrap_z g Hg32) as ((_ & S1) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small g) in Hc by lia.
  apply Z.eqb_neq in Hc.
  assert (Hg0 : g <> 0) by (intros Eg; apply Hc; exact (S1 Eg)). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SUBR.
  { d_awrw U20' U9'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U20'' : bv_unsigned (ew E2 20) = F + 32) by (rewrite (HE2 20%nat) by lia; exact U20).
  assert (U9'' : bv_unsigned (ew E2 9) = sp1) by (rewrite (HE2 9%nat) by lia; exact U9).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) ->
    ~ (sp1 + 24 <= a < sp1 + 32) -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1 H2 H3.
    apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
      [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
    intros b wlo whi y Hiw Hy. cbv beta.
    op_win Hiw Hy ltac:(rewrite ?U20'', ?U9'' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  destruct (d_ck E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ (SAlu ALU_AND (SOff 33 0) (SLit 1)) kv av RG1 RG2
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    U20'' (U_atom E2 11 kv ltac:(rewrite (HE2 11%nat) by lia; exact E11) ltac:(lia))
    (U_atom E2 12 av ltac:(rewrite (HE2 12%nat) by lia; exact E12) ltac:(lia)) Hkv Hav) as (VD & VK).
  rewrite (d_disp E2 db ltac:(rewrite (HE2 33%nat) by lia; exact E33) Hdb) in VD.
  clear HF HFr HG RG1 RG2.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 g; w64 db; w64 0; w64 0] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 0) Q23 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 24) (w64 (x + 1)) Q24
    ltac:(rewrite (op_den _ E0 24 1 x HE2 ltac:(lia) E24 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); reflexivity).
  op_reg HS (Z_to_bv 5 20) (w64 (F + 32)) Q20
    ltac:(rewrite (op_den _ E0 20 0 (F + 32) HE2 ltac:(lia) E20 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBR HJ).
  + left. split; [reflexivity|]. split; [exact Hg0|]. split; [exact Q11|]. split; [exact Q24|].
    split; [exact Q23|]. split; [exact Q20 | exact Q22].
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H20 H22 H23 H24 H25;
      first [exfalso; lia | apply HKR; vm_compute; reflexivity].
  + exact VD.
  + exact VK.
  + intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 H2 H3). exact (KR1 a Ha H1 H2 H3).
  + intros a Ha. exact (GA2 a (GA1 a Ha)).
Qed.

(* The length word the `slli` / `or` at +0x12b4 / +0x12b8 leave: the low byte alone (atom 34), or the high byte
   (atom 35) shifted by 8 or'ed with the low byte. *)
Lemma d_or1 : forall E lo, ew E 34 = w64 lo -> 0 <= lo < 256 ->
  sv_denot E (SAlu ALU_OR (SLit 0) (SOff 34 0)) = w64 lo.
Proof.
intros E lo H Hl. rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_lit E 0) by lia. rewrite (U_atom E 34 lo H ltac:(lia)). rewrite Z.lor_0_l. apply zcanon_id. unfold M64. lia.
Qed.
Lemma d_or2 : forall E lo hi, ew E 34 = w64 lo -> ew E 35 = w64 hi -> 0 <= lo < 256 -> 0 <= hi < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 34 0)) = w64 (lo + 256 * hi).
Proof.
intros E lo hi H34 H35 Hl Hh. rewrite denot_lit_U. unfold w64. f_equal. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_lit E 8) by lia. rewrite (U_atom E 34 lo H34 ltac:(lia)), (U_atom E 35 hi H35 ltac:(lia)).
change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (hi * 2 ^ 8)) by (unfold M64; lia).
rewrite (op_lor_sh 8 hi lo ltac:(lia) ltac:(lia) ltac:(lia)). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* Stage D when two bytes are left after the key bytes (s7 = 2): the display byte, g_raw, c + 25, s6 = 1, `beqz
   g_raw`: SUBT (+0xd14) or SUBR (`beqz s6` not taken, the checked load of the length word's low byte +0xb60, `bne
   s6, 1` not taken, +0xb7c .. +0xb8c, +0x12b4: a1 = the low byte, s8 = x + 2, s7 = 0, s4 = c). *)
Lemma op4_d2 : forall regs mem md x g kv av db lo (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 (F + 32) -> YK11.getr regs 11 = w64 kv ->
  YK11.getr regs 12 = w64 av -> YK11.getr regs 24 = w64 x -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 2 ->
  0 <= kv < 256 -> 0 <= av < 256 -> 4096 <= x -> x + 2 <= PTRF ->
  (x + 2 <= kLowShadowBeg \/ kHighMemBeg <= x) ->
  (x + 2 <= F \/ F + 256 <= x) -> x + 2 <= sp1 -> (x + 2 <= TB_g_raw \/ TB_g_raw + 4 <= x) ->
  rdword (rdv mem) (sp1 + 104) = Some PG_RAW -> rdword (rdv mem) (sp1 + 144) = Some (F + 32) ->
  val_mem segs (mrestrict (w_H W) mem) TB_g_raw 4 g -> 0 <= g < 2 ^ 32 ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  (forall a, F + 57 <= a < F + 64 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 8 -> rdv mem (SHF + i) = Some 0) ->
  val_mem segs (mrestrict (w_H W) mem) x 1 db -> 0 <= db < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (x + 1) 1 lo -> 0 <= lo < 256 ->
  range_addressable (rdv mem) SHADOW_OFF x 2 ->
  d_post regs mem g (Z.land db 1) (DSpec.KEY (kv mod 9 + 1) av) lo (x + 2) 0 (x + 1) 1 Q ->
  SRr segs W (at_ O_KEY regs mem md) Q.
Proof.
intros regs mem md x g kv av db lo Q HJ R9 R20 R11 R12 R24 R26 R22 R23 Hkv Hav Hx1 Hx2 Happ Hfr Hsp Hgr H104 H144 HGV
  Hg32 Psp Pc HZS Vdb Hdb Vlo Hlo HRA HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
destruct (op_frame_pres mem md HJ) as (_ & _ & HFapp).
pose proof (sd_entry regs mem x g kv av db lo 0 R9 R20 R11 R12 R24 R26 Hkv Hav ltac:(lia) H104 H144 HGV Hg32 Psp Pc
  Hdb Hlo ltac:(lia)) as H0.
set (E0 := op_E regs [w64 g; w64 db; w64 lo; w64 0]) in H0.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (E9 : ew E0 9 = w64 sp1) by (unfold E0; rewrite (op_ew regs _ 9 9%bv eq_refl); exact R9).
assert (E20 : ew E0 20 = w64 (F + 32)) by (unfold E0; rewrite (op_ew regs _ 20 20%bv eq_refl); exact R20).
assert (E11 : ew E0 11 = w64 kv) by (unfold E0; rewrite (op_ew regs _ 11 11%bv eq_refl); exact R11).
assert (E12 : ew E0 12 = w64 av) by (unfold E0; rewrite (op_ew regs _ 12 12%bv eq_refl); exact R12).
assert (E24 : ew E0 24 = w64 x) by (unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E0 26 = w64 SHADOW_OFF) by (unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26).
assert (E21 : ew E0 21 = YK11.getr regs 21) by (unfold E0; exact (op_ew regs _ 21 21%bv eq_refl)).
assert (E32 : ew E0 32 = w64 g) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E33 : ew E0 33 = w64 db) by (unfold E0; exact (op_ewx regs _ 1 ltac:(lia))).
assert (E34 : ew E0 34 = w64 lo) by (unfold E0; exact (op_ewx regs _ 2 ltac:(lia))).
assert (U9 : bv_unsigned (ew E0 9) = sp1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E0 20) = F + 32) by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E0 24) = x) by (rewrite E24; unfold w64; apply unsigned_lit_small; unfold PTRF in *; lia).
assert (Hwin : region_ok segs E0 (mrestrict (w_H W) mem) (d_win 2)).
{ unfold d_win, region_ok.
  cbn [firstn d_ch YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_nat].
  rewrite U24. split; [lia|]. split; [unfold PTRF in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val segs E0 _ x 0 1 (SOff 33 0) db); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vdb].
    cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - apply (chunk_ok_val segs E0 _ x 1 1 (SOff 34 0) lo); [| cbn; lia | cbn; lia | exact Vlo].
    cbn [sv_denot]. rewrite E34, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hdis : all_disjoint E0 (d_win 2) (ss_mem ss_d0)).
{ apply all_disjoint_of_extents.
  unfold ss_d0, d_base, d_win, d_rc25, d_rc28, d_r104, d_rg, d_r144, d_r24, extent_of_region.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_nat]. rewrite U24, U9, U20.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold TB_g_raw in *. repeat split; lia. }
pose proof (st_ok_pi_add_region _ _ _ (d_win 2) H0 eq_refl Hwin Hdis) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 22) 1 H1 R22 eq_refl) as H2.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 23) 2 H2 R23 eq_refl) as HS. clear H0 H1 H2.
assert (SHOK : sh_ok segs K_Bx (D_SH 2) E0 (mrestrict (w_H W) mem)).
{ unfold D_SH. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range segs (w_H W) mem E0 K_Bx 24%nat x 2 x 0 (Z.of_nat 2) HRA).
    + unfold K_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E24 | unfold PTRF in *; lia].
    + lia.
    + cbn. lia.
    + intros y Hy. cbn [Z.min Z.max Z.of_nat] in Hy. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, PTRF in *. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E0 K_Bx 20%nat (F + 57) 7 (F + 32) 25 32).
    + apply (TGNA.frame_ra_zero _ F (F + 57) 7 7 8); [lia | exact F8m | lia | lia |].
      intros i Hi. exact (HZS i ltac:(lia)).
    + unfold K_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E20 | lia].
    + lia.
    + lia.
    + intros y Hy. cbn [Z.min Z.max] in Hy. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
      unfold SHADOW_OFF. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ d_awrw U20 U9. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U20' : bv_unsigned (ew E1 20) = F + 32) by (rewrite (HE1 20%nat) by lia; exact U20).
assert (U9' : bv_unsigned (ew E1 9) = sp1) by (rewrite (HE1 9%nat) by lia; exact U9).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 24 <= a < sp1 + 32) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
    [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
  intros b wlo whi y Hiw Hy. cbv beta.
  op_win Hiw Hy ltac:(rewrite ?U20', ?U9' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename ms into ms1.
assert (U32' : U E1 (SOff 32 0) = g)
  by (apply U_atom; [rewrite (HE1 32%nat) by lia; exact E32 | lia]).
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* g_raw = 0: SUBT *)
  destruct (op_swrap_z g Hg32) as ((S1 & _) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small g) in Hc by lia.
  apply Z.eqb_eq in Hc. apply S1 in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SUBT.
  { d_awrw U20' U9'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U20'' : bv_unsigned (ew E2 20) = F + 32) by (rewrite (HE2 20%nat) by lia; exact U20).
  assert (U9'' : bv_unsigned (ew E2 9) = sp1) by (rewrite (HE2 9%nat) by lia; exact U9).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) ->
    ~ (sp1 + 24 <= a < sp1 + 32) -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1 H2 H3.
    apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
      [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
    intros b wlo whi y Hiw Hy. cbv beta.
    op_win Hiw Hy ltac:(rewrite ?U20'', ?U9'' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  destruct (d_ck E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ (SAlu ALU_AND (SOff 33 0) (SLit 1)) kv av RG1 RG2
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    U20'' (U_atom E2 11 kv ltac:(rewrite (HE2 11%nat) by lia; exact E11) ltac:(lia))
    (U_atom E2 12 av ltac:(rewrite (HE2 12%nat) by lia; exact E12) ltac:(lia)) Hkv Hav) as (VD & VK).
  rewrite (d_disp E2 db ltac:(rewrite (HE2 33%nat) by lia; exact E33) Hdb) in VD.
  pose proof (st_ok_pi_region_nth _ _ _ 6 _ HS eq_refl) as RG6. cbn [ms_mem restrict] in RG6.
  pose proof (op_chunk_val E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ 24 8 (SOff 21 0) RG6
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VS.
  cbn [base_val] in VS. rewrite U9'' in VS.
  assert (E21' : ew E2 21 = YK11.getr regs 21) by exact (eq_trans (HE2 21%nat ltac:(lia)) E21).
  replace (bv_unsigned (sv_denot E2 (SOff 21 0)) mod 2 ^ (8 * Z.of_N 8)) with (bv_unsigned (YK11.getr regs 21)) in VS.
  2: { cbn [sv_denot]. rewrite E21'.
       rewrite Z.add_0_r, Z_to_bv_bv_unsigned. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 21)) as Hr.
       change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
       rewrite Z.mod_small by lia. reflexivity. }
  change (N.to_nat 8) with 8%nat in VS.
  clear HF HFr HG RG6 RG1 RG2.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 g; w64 db; w64 lo; w64 0] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 25) (w64 (x + 1)) Q25
    ltac:(rewrite (op_den _ E0 24 1 x HE2 ltac:(lia) E24 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 20) (w64 1) Q20 ltac:(reflexivity).
  apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBT HJ).
  + right. split; [reflexivity|]. split; [exact Hc|]. split; [exact Q25|]. split; [exact Q22|].
    split; [exact Q20|].
    apply YF0x.val_mem_rdword; [|exact VS]. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 21)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H20 H22 H23 H24 H25;
      first [exfalso; lia | apply HKR; vm_compute; reflexivity].
  + exact VD.
  + exact VK.
  + intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 H2 H3). exact (KR1 a Ha H1 H2 H3).
  + intros a Ha. exact (GA2 a (GA1 a Ha)).
- (* g_raw <> 0: SUBR *)
  destruct (op_swrap_z g Hg32) as ((_ & S1) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small g) in Hc by lia.
  apply Z.eqb_neq in Hc.
  assert (Hg0 : g <> 0) by (intros Eg; apply Hc; exact (S1 Eg)). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SUBR.
  { d_awrw U20' U9'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U20'' : bv_unsigned (ew E2 20) = F + 32) by (rewrite (HE2 20%nat) by lia; exact U20).
  assert (U9'' : bv_unsigned (ew E2 9) = sp1) by (rewrite (HE2 9%nat) by lia; exact U9).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) ->
    ~ (sp1 + 24 <= a < sp1 + 32) -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1 H2 H3.
    apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
      [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
    intros b wlo whi y Hiw Hy. cbv beta.
    op_win Hiw Hy ltac:(rewrite ?U20'', ?U9'' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  destruct (d_ck E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ (SAlu ALU_AND (SOff 33 0) (SLit 1)) kv av RG1 RG2
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    U20'' (U_atom E2 11 kv ltac:(rewrite (HE2 11%nat) by lia; exact E11) ltac:(lia))
    (U_atom E2 12 av ltac:(rewrite (HE2 12%nat) by lia; exact E12) ltac:(lia)) Hkv Hav) as (VD & VK).
  rewrite (d_disp E2 db ltac:(rewrite (HE2 33%nat) by lia; exact E33) Hdb) in VD.
  clear HF HFr HG RG1 RG2.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 g; w64 db; w64 lo; w64 0] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 11) (w64 lo) Q11
    ltac:(first [exact (d_or1 E2 lo ltac:(rewrite (HE2 34%nat) by lia; exact E34) Hlo)
               | rewrite (op_den _ E0 34 0 lo HE2 ltac:(lia) E34 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity]).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 0) Q23 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 24) (w64 (x + 2)) Q24
    ltac:(rewrite (op_den _ E0 24 2 x HE2 ltac:(lia) E24 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); reflexivity).
  op_reg HS (Z_to_bv 5 20) (w64 (F + 32)) Q20
    ltac:(rewrite (op_den _ E0 20 0 (F + 32) HE2 ltac:(lia) E20 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBR HJ).
  + left. split; [reflexivity|]. split; [exact Hg0|]. split; [exact Q11|]. split; [exact Q24|].
    split; [exact Q23|]. split; [exact Q20 | exact Q22].
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H20 H22 H23 H24 H25;
      first [exfalso; lia | apply HKR; vm_compute; reflexivity].
  + exact VD.
  + exact VK.
  + intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 H2 H3). exact (KR1 a Ha H1 H2 H3).
  + intros a Ha. exact (GA2 a (GA1 a Ha)).
Qed.

(* Stage D when three or more bytes are left after the key bytes (s7 = n in [3, 2 ^ 26]): the display byte, g_raw,
   c + 25, s6 = n - 1, `beqz g_raw`: SUBT (+0xd14) or SUBR (the low byte +0xb60, `bne s6, 1` taken, the UBSan test
   +0x1294 and the checked load of the high byte +0x12a0, +0x12b4: a1 = low + 256 high, s8 = x + 3, s7 = n - 3). *)
Lemma op4_d3 : forall regs mem md x n g kv av db lo hi (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 (F + 32) -> YK11.getr regs 11 = w64 kv ->
  YK11.getr regs 12 = w64 av -> YK11.getr regs 24 = w64 x -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 n -> 3 <= n <= 2 ^ 26 ->
  0 <= kv < 256 -> 0 <= av < 256 -> 4096 <= x -> x + 3 <= PTRF ->
  (x + 3 <= kLowShadowBeg \/ kHighMemBeg <= x) ->
  (x + 3 <= F \/ F + 256 <= x) -> x + 3 <= sp1 -> (x + 3 <= TB_g_raw \/ TB_g_raw + 4 <= x) ->
  rdword (rdv mem) (sp1 + 104) = Some PG_RAW -> rdword (rdv mem) (sp1 + 144) = Some (F + 32) ->
  val_mem segs (mrestrict (w_H W) mem) TB_g_raw 4 g -> 0 <= g < 2 ^ 32 ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  (forall a, F + 57 <= a < F + 64 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 8 -> rdv mem (SHF + i) = Some 0) ->
  val_mem segs (mrestrict (w_H W) mem) x 1 db -> 0 <= db < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (x + 1) 1 lo -> 0 <= lo < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (x + 2) 1 hi -> 0 <= hi < 256 ->
  range_addressable (rdv mem) SHADOW_OFF x 3 ->
  d_post regs mem g (Z.land db 1) (DSpec.KEY (kv mod 9 + 1) av) (lo + 256 * hi) (x + 3) (n - 3) (x + 1) (n - 1) Q ->
  SRr segs W (at_ O_KEY regs mem md) Q.
Proof.
intros regs mem md x n g kv av db lo hi Q HJ R9 R20 R11 R12 R24 R26 R22 R23 Hn Hkv Hav Hx1 Hx2 Happ Hfr Hsp Hgr H104
  H144 HGV Hg32 Psp Pc HZS Vdb Hdb Vlo Hlo Vhi Hhi HRA HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
destruct (op_frame_pres mem md HJ) as (_ & _ & HFapp).
pose proof (sd_entry regs mem x g kv av db lo hi R9 R20 R11 R12 R24 R26 Hkv Hav ltac:(lia) H104 H144 HGV Hg32 Psp Pc
  Hdb Hlo Hhi) as H0.
set (E0 := op_E regs [w64 g; w64 db; w64 lo; w64 hi]) in H0.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (E9 : ew E0 9 = w64 sp1) by (unfold E0; rewrite (op_ew regs _ 9 9%bv eq_refl); exact R9).
assert (E20 : ew E0 20 = w64 (F + 32)) by (unfold E0; rewrite (op_ew regs _ 20 20%bv eq_refl); exact R20).
assert (E11 : ew E0 11 = w64 kv) by (unfold E0; rewrite (op_ew regs _ 11 11%bv eq_refl); exact R11).
assert (E12 : ew E0 12 = w64 av) by (unfold E0; rewrite (op_ew regs _ 12 12%bv eq_refl); exact R12).
assert (E23 : ew E0 23 = w64 n) by (unfold E0; rewrite (op_ew regs _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E0 24 = w64 x) by (unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E0 26 = w64 SHADOW_OFF) by (unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26).
assert (E21 : ew E0 21 = YK11.getr regs 21) by (unfold E0; exact (op_ew regs _ 21 21%bv eq_refl)).
assert (E32 : ew E0 32 = w64 g) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E33 : ew E0 33 = w64 db) by (unfold E0; exact (op_ewx regs _ 1 ltac:(lia))).
assert (E34 : ew E0 34 = w64 lo) by (unfold E0; exact (op_ewx regs _ 2 ltac:(lia))).
assert (E35 : ew E0 35 = w64 hi) by (unfold E0; exact (op_ewx regs _ 3 ltac:(lia))).
assert (U9 : bv_unsigned (ew E0 9) = sp1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E0 20) = F + 32) by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E0 23) = n) by (rewrite E23; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E0 24) = x) by (rewrite E24; unfold w64; apply unsigned_lit_small; unfold PTRF in *; lia).
assert (Hwin : region_ok segs E0 (mrestrict (w_H W) mem) (d_win 3)).
{ unfold d_win, region_ok.
  cbn [firstn d_ch YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_nat].
  rewrite U24. split; [lia|]. split; [unfold PTRF in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_ok_val segs E0 _ x 0 1 (SOff 33 0) db); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vdb].
    cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - apply (chunk_ok_val segs E0 _ x 1 1 (SOff 34 0) lo); [| cbn; lia | cbn; lia | exact Vlo].
    cbn [sv_denot]. rewrite E34, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - apply (chunk_ok_val segs E0 _ x 2 1 (SOff 35 0) hi); [| cbn; lia | cbn; lia | exact Vhi].
    cbn [sv_denot]. rewrite E35, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hdis : all_disjoint E0 (d_win 3) (ss_mem ss_d0)).
{ apply all_disjoint_of_extents.
  unfold ss_d0, d_base, d_win, d_rc25, d_rc28, d_r104, d_rg, d_r144, d_r24, extent_of_region.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_nat]. rewrite U24, U9, U20.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold TB_g_raw in *. repeat split; lia. }
pose proof (st_ok_pi_add_region _ _ _ (d_win 3) H0 eq_refl Hwin Hdis) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 22) 1 H1 R22 eq_refl) as H2.
assert (Hf23 : afact_ok E0 23 (mkAF 3 (2 ^ 26) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pose proof (st_ok_pi_add_fact _ _ _ 23 _ H2 Hf23) as HS. clear H0 H1 H2.
assert (SHOK : sh_ok segs K_Bx (D_SH 3) E0 (mrestrict (w_H W) mem)).
{ unfold D_SH. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range segs (w_H W) mem E0 K_Bx 24%nat x 3 x 0 (Z.of_nat 3) HRA).
    + unfold K_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E24 | unfold PTRF in *; lia].
    + lia.
    + cbn. lia.
    + intros y Hy. cbn [Z.min Z.max Z.of_nat] in Hy. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, PTRF in *. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E0 K_Bx 20%nat (F + 57) 7 (F + 32) 25 32).
    + apply (TGNA.frame_ra_zero _ F (F + 57) 7 7 8); [lia | exact F8m | lia | lia |].
      intros i Hi. exact (HZS i ltac:(lia)).
    + unfold K_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E20 | lia].
    + lia.
    + lia.
    + intros y Hy. cbn [Z.min Z.max] in Hy. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
      unfold SHADOW_OFF. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ d_awrw U20 U9. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U20' : bv_unsigned (ew E1 20) = F + 32) by (rewrite (HE1 20%nat) by lia; exact U20).
assert (U9' : bv_unsigned (ew E1 9) = sp1) by (rewrite (HE1 9%nat) by lia; exact U9).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 24 <= a < sp1 + 32) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
    [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
  intros b wlo whi y Hiw Hy. cbv beta.
  op_win Hiw Hy ltac:(rewrite ?U20', ?U9' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename ms into ms1.
assert (U32' : U E1 (SOff 32 0) = g)
  by (apply U_atom; [rewrite (HE1 32%nat) by lia; exact E32 | lia]).
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* g_raw = 0: SUBT *)
  destruct (op_swrap_z g Hg32) as ((S1 & _) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small g) in Hc by lia.
  apply Z.eqb_eq in Hc. apply S1 in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SUBT.
  { d_awrw U20' U9'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U20'' : bv_unsigned (ew E2 20) = F + 32) by (rewrite (HE2 20%nat) by lia; exact U20).
  assert (U9'' : bv_unsigned (ew E2 9) = sp1) by (rewrite (HE2 9%nat) by lia; exact U9).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) ->
    ~ (sp1 + 24 <= a < sp1 + 32) -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1 H2 H3.
    apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
      [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
    intros b wlo whi y Hiw Hy. cbv beta.
    op_win Hiw Hy ltac:(rewrite ?U20'', ?U9'' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  destruct (d_ck E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ (SAlu ALU_AND (SOff 33 0) (SLit 1)) kv av RG1 RG2
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    U20'' (U_atom E2 11 kv ltac:(rewrite (HE2 11%nat) by lia; exact E11) ltac:(lia))
    (U_atom E2 12 av ltac:(rewrite (HE2 12%nat) by lia; exact E12) ltac:(lia)) Hkv Hav) as (VD & VK).
  rewrite (d_disp E2 db ltac:(rewrite (HE2 33%nat) by lia; exact E33) Hdb) in VD.
  pose proof (st_ok_pi_region_nth _ _ _ 6 _ HS eq_refl) as RG6. cbn [ms_mem restrict] in RG6.
  pose proof (op_chunk_val E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ 24 8 (SOff 21 0) RG6
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VS.
  cbn [base_val] in VS. rewrite U9'' in VS.
  assert (E21' : ew E2 21 = YK11.getr regs 21) by exact (eq_trans (HE2 21%nat ltac:(lia)) E21).
  replace (bv_unsigned (sv_denot E2 (SOff 21 0)) mod 2 ^ (8 * Z.of_N 8)) with (bv_unsigned (YK11.getr regs 21)) in VS.
  2: { cbn [sv_denot]. rewrite E21'.
       rewrite Z.add_0_r, Z_to_bv_bv_unsigned. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 21)) as Hr.
       change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
       rewrite Z.mod_small by lia. reflexivity. }
  change (N.to_nat 8) with 8%nat in VS.
  clear HF HFr HG RG6 RG1 RG2.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 g; w64 db; w64 lo; w64 hi] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 25) (w64 (x + 1)) Q25
    ltac:(rewrite (op_den _ E0 24 1 x HE2 ltac:(lia) E24 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); reflexivity).
  op_reg HS (Z_to_bv 5 22) (w64 (n - 1)) Q22
    ltac:(rewrite (op_den _ E0 23 (-1) n HE2 ltac:(lia) E23 ltac:(lia) ltac:(lia)); f_equal; lia).
  op_reg HS (Z_to_bv 5 20) (w64 1) Q20 ltac:(reflexivity).
  apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBT HJ).
  + right. split; [reflexivity|]. split; [exact Hc|]. split; [exact Q25|]. split; [exact Q22|].
    split; [exact Q20|].
    apply YF0x.val_mem_rdword; [|exact VS]. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 21)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H20 H22 H23 H24 H25;
      first [exfalso; lia | apply HKR; vm_compute; reflexivity].
  + exact VD.
  + exact VK.
  + intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 H2 H3). exact (KR1 a Ha H1 H2 H3).
  + intros a Ha. exact (GA2 a (GA1 a Ha)).
- (* g_raw <> 0: SUBR *)
  destruct (op_swrap_z g Hg32) as ((_ & S1) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small g) in Hc by lia.
  apply Z.eqb_neq in Hc.
  assert (Hg0 : g <> 0) by (intros Eg; apply Hc; exact (S1 Eg)). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SUBR.
  { d_awrw U20' U9'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U20'' : bv_unsigned (ew E2 20) = F + 32) by (rewrite (HE2 20%nat) by lia; exact U20).
  assert (U9'' : bv_unsigned (ew E2 9) = sp1) by (rewrite (HE2 9%nat) by lia; exact U9).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) ->
    ~ (sp1 + 24 <= a < sp1 + 32) -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1 H2 H3.
    apply (kept_of_frame _ _ _ _ _ (fun y => y = F + 57 \/ (F + 60 <= y < F + 64) \/ (sp1 + 24 <= y < sp1 + 32)) HFr);
      [| exact Ha | intros [Hy | [Hy | Hy]]; [exact (H1 Hy) | exact (H2 Hy) | exact (H3 Hy)]].
    intros b wlo whi y Hiw Hy. cbv beta.
    op_win Hiw Hy ltac:(rewrite ?U20'', ?U9'' in Hy; first [left; lia | right; left; lia | right; right; lia]). }
  assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  destruct (d_ck E2 (w_H W) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ (SAlu ALU_AND (SOff 33 0) (SLit 1)) kv av RG1 RG2
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    U20'' (U_atom E2 11 kv ltac:(rewrite (HE2 11%nat) by lia; exact E11) ltac:(lia))
    (U_atom E2 12 av ltac:(rewrite (HE2 12%nat) by lia; exact E12) ltac:(lia)) Hkv Hav) as (VD & VK).
  rewrite (d_disp E2 db ltac:(rewrite (HE2 33%nat) by lia; exact E33) Hdb) in VD.
  clear HF HFr HG RG1 RG2.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 g; w64 db; w64 lo; w64 hi] (ss_regs ssx) _ r
      (fun m Hm => HE2 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  pmkst HS.
  op_reg HS (Z_to_bv 5 11) (w64 (lo + 256 * hi)) Q11
    ltac:(exact (d_or2 E2 lo hi ltac:(rewrite (HE2 34%nat) by lia; exact E34)
                   ltac:(rewrite (HE2 35%nat) by lia; exact E35) Hlo Hhi)).
  op_reg HS (Z_to_bv 5 22) (w64 1) Q22 ltac:(reflexivity).
  op_reg HS (Z_to_bv 5 23) (w64 (n - 3)) Q23
    ltac:(rewrite (op_den _ E0 23 (-3) n HE2 ltac:(lia) E23 ltac:(lia) ltac:(lia)); f_equal; lia).
  op_reg HS (Z_to_bv 5 24) (w64 (x + 3)) Q24
    ltac:(rewrite (op_den _ E0 24 3 x HE2 ltac:(lia) E24 ltac:(unfold PTRF in *; lia)
            ltac:(unfold PTRF in *; lia)); reflexivity).
  op_reg HS (Z_to_bv 5 20) (w64 (F + 32)) Q20
    ltac:(rewrite (op_den _ E0 20 0 (F + 32) HE2 ltac:(lia) E20 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity).
  apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBR HJ).
  + left. split; [reflexivity|]. split; [exact Hg0|]. split; [exact Q11|]. split; [exact Q24|].
    split; [exact Q23|]. split; [exact Q20 | exact Q22].
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H20 H22 H23 H24 H25;
      first [exfalso; lia | apply HKR; vm_compute; reflexivity].
  + exact VD.
  + exact VK.
  + intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 H2 H3). exact (KR1 a Ha H1 H2 H3).
  + intros a Ha. exact (GA2 a (GA1 a Ha)).
Qed.

(* ------------------------------------------------------------------ *)
(* The stages composed: the arm to SUBR / SUBT                          *)
(* ------------------------------------------------------------------ *)

(* The machine stack of the journal's window is present. *)
Lemma op_stack_pres : forall m md, J m md -> forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) m a.
Proof.
intros m md HJ a Ha. pose proof HJ as (HSTKJ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact (Hpres a Ha).
Qed.

(* The input's bytes, as garr8 of the caller's input states them. *)
Lemma op_g8 : forall m p (D : list byte) (j : nat),
  garr8 segs (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) D) -> (j < length D)%nat ->
  val_mem segs (mrestrict (w_H W) m) (p + Z.of_nat j) 1 (DSpec.at8 D j) /\ 0 <= DSpec.at8 D j < 256.
Proof.
intros m p D j HG Hj. rewrite <- (length_map (fun b : byte => bv_unsigned b) D) in Hj.
destruct (HG j Hj) as [Hv Hr].
assert (E : nth j (map (fun b : byte => bv_unsigned b) D) 0 = DSpec.at8 D j).
{ unfold DSpec.at8, DSpec.bz. rewrite <- (map_nth (fun b : byte => bv_unsigned b) D (DSpec.b8 0) j). reflexivity. }
rewrite E in Hv, Hr. exact (conj Hv Hr).
Qed.

Lemma op_twin_G : forall a, tw_in TMAP_B a -> inG TG.G_HARNESS_B a.
Proof. intros a (o & b & n & Hin & Ha). exact (op_inG_row o b n a Hin Ha). Qed.
Lemma op_inG_OW : forall a, TB_OW <= a < TB_OW + 304 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (op_inG_row _ _ _ a TMAP_B_OW). unfold TW.SZ_OW. lia. Qed.
Lemma op_inG_GOT : forall a, TB_GOT <= a < TB_GOT + 224 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (op_inG_row _ _ _ a TMAP_B_GOT). unfold TW.SZ_GOT. lia. Qed.
Lemma op_inG_M : forall a, TB_M + 88 <= a < TB_M + 92 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (op_inG_row _ _ _ a TMAP_B_M). unfold TW.SZ_M. lia. Qed.
Lemma op_inG_raw : forall a, TB_g_raw <= a < TB_g_raw + 4 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (op_inG_row _ _ _ a TMAP_B_g_raw). unfold TW.SZ_g_raw. lia. Qed.

(* Where the bytes of G, the frame's shadow, the stack from sp1 to sp0, the blocks and the frame past c lie: apart
   from what the segment writes outside G (the shadow bytes 4 .. 7, c, 24(s1), the memsets' stack window). *)
Lemma op_G_apart : forall m md, J m md -> forall a, inG TG.G_HARNESS_B a ->
  0 <= a < 2 ^ 64 /\ ~ (SHF + 4 <= a < SHF + 8) /\ ~ (F + 32 <= a < F + 64) /\
  ~ (sp1 + 24 <= a < sp1 + 32) /\ ~ (sp1 - ESTACK <= a < sp1).
Proof.
intros m md HJ a Ha. pose proof (op_G_low a Ha) as Hl. pose proof (op_G_frame m md HJ a Ha) as Hf.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (_ & _ & F8b).
unfold kLowMemEnd, ESTACK, SHADOW_OFF in *. repeat split; lia.
Qed.
Lemma op_SH_apart : forall m md, J m md -> forall i, 0 <= i < 32 ->
  0 <= SHF + i < 2 ^ 64 /\ ~ inG TG.G_HARNESS_B (SHF + i) /\ ~ (F + 32 <= SHF + i < F + 64) /\
  ~ (sp1 + 24 <= SHF + i < sp1 + 32) /\ ~ (sp1 - ESTACK <= SHF + i < sp1).
Proof.
intros m md HJ i Hi. destruct (op_frame_pres m md HJ) as (_ & _ & Happ).
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (NG : ~ inG TG.G_HARNESS_B (SHF + i)).
{ intros HG. pose proof (op_G_low _ HG) as Hl. unfold kLowMemEnd, SHADOW_OFF in *. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold ESTACK, SHADOW_OFF in *.
split; [lia|]. split; [exact NG|]. repeat split; lia.
Qed.
Lemma op_stk_apart : forall a, sp1 <= a <= sp0 ->
  0 <= a < 2 ^ 64 /\ ~ inG TG.G_HARNESS_B a /\ ~ (SHF + 4 <= a < SHF + 8) /\ ~ (F + 32 <= a < F + 64) /\
  ~ (sp1 - ESTACK <= a < sp1).
Proof.
intros a Ha. pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (_ & _ & F8b).
assert (NG : ~ inG TG.G_HARNESS_B a) by (intros HG; pose proof (op_G_low _ HG) as Hl; unfold kLowMemEnd in *; lia).
unfold ESTACK, SHADOW_OFF. split; [lia|]. split; [exact NG|]. repeat split; lia.
Qed.
Lemma op_blk_apart : forall m md b n, J m md -> In (b, n) (ablocks B ly S) -> forall j, 0 <= j < req_size n ->
  0 <= b + j < 2 ^ 64 /\ ~ inG TG.G_HARNESS_B (b + j) /\ ~ (SHF + 4 <= b + j < SHF + 8) /\
  ~ (F + 32 <= b + j < F + 64) /\ ~ (sp1 + 24 <= b + j < sp1 + 32) /\ ~ (sp1 - ESTACK <= b + j < sp1).
Proof.
intros m md b n HJ Hin j Hj.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof (sep_block_frame segs B LAWS ly S W m md b n LF_CID pos HAR Hin HFIN) as Hsep.
rewrite HFA in Hsep. change (fs_frame_bytes LF_CID) with 256 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (NG : ~ inG TG.G_HARNESS_B (b + j)).
{ intros HG. apply (blk_img segs B LAWS ly S W m md b n (b + j) HAR Hin ltac:(lia)). exact (trans_g_img _ HG). }
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold ESTACK, SHADOW_OFF in *.
split; [lia|]. split; [exact NG|]. repeat split; lia.
Qed.
Lemma op_ftail_apart : forall m md a, J m md -> F + 64 <= a < F + 256 ->
  0 <= a < 2 ^ 64 /\ ~ inG TG.G_HARNESS_B a /\ ~ (SHF + 4 <= a < SHF + 8) /\ ~ (F + 32 <= a < F + 64) /\
  ~ (sp1 + 24 <= a < sp1 + 32) /\ ~ (sp1 - ESTACK <= a < sp1).
Proof.
intros m md a HJ Ha. destruct (op_frame_pres m md HJ) as (_ & _ & Happ).
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (NG : ~ inG TG.G_HARNESS_B a) by (intros HG; exact (op_G_frame m md HJ a HG ltac:(lia))).
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold ESTACK, SHADOW_OFF in *.
split; [lia|]. split; [exact NG|]. repeat split; lia.
Qed.

Lemma op_rdw_kept : forall m m' a v, (forall k, 0 <= k < 8 -> rdv m' (a + k) = rdv m (a + k)) ->
  rdword (rdv m) a = Some v -> rdword (rdv m') a = Some v.
Proof. intros m m' a v Hk Hv. rewrite (rdword_ext (rdv m) (rdv m') a Hk). exact Hv. Qed.

(* Byte j of c at a memory. *)
Lemma op_c_garr8 : forall m disp key, 0 <= disp < 256 ->
  (forall j, (j < 32)%nat -> rdv m (F + 32 + Z.of_nat j) =
     Some (if (j =? 25)%nat then disp else if (j <? 28)%nat then 0 else YO0f.le_byte key 4 (j - 28))) ->
  garr8 segs (mrestrict (w_H W) m) (F + 32) (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 disp key)).
Proof.
intros m disp key Hd Hv. unfold garr8. intros j Hj.
assert (HL : length (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 disp key)) = 32%nat).
{ unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, repeat_length, TWL.length_put. reflexivity. }
rewrite HL in Hj. rewrite (op_cmd_nth disp key j Hd Hj).
split.
- apply YE36.val_mem1_of_aview. exact (Hv j Hj).
- destruct (j =? 25)%nat; [lia|]. destruct (j <? 28)%nat; [lia|]. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* Two bytes of an input block apart from g_raw (a byte of the image). *)
Lemma op_blk_raw : forall m md b n q kk, J m md -> In (b, n) (ablocks B ly S) -> b <= q -> q + kk <= b + req_size n ->
  0 < kk -> q + kk <= TB_g_raw \/ TB_g_raw + 4 <= q.
Proof.
intros m md b n q kk HJ Hin H1 H2 Hk.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (Z_le_gt_dec (q + kk) TB_g_raw) as [Hl | Hl]; [left; exact Hl|].
destruct (Z_le_gt_dec (TB_g_raw + 4) q) as [Hr | Hr]; [right; exact Hr|].
exfalso.
assert (Hy : b <= Z.max q TB_g_raw < b + req_size n) by lia.
apply (blk_img segs B LAWS ly S W m md b n (Z.max q TB_g_raw) HAR Hin Hy).
apply trans_g_img. apply op_inG_raw. lia.
Qed.

(* What the segment leaves for the cut at SUBR / SUBT, from the arm's registers regs and memory mem, the start world
   Bw, the input D at p and the cursor c0 before the op byte. *)
Definition op4_post (regs : bvmap 5 word) (mem : word -> option byte) (Bw : list byte) (p : Z) (D : list byte)
    (c0 : TOP.fuzz_in) (Q : world segs -> config -> Prop) : Prop :=
  forall regs2 mem2 md2 pc B4, J mem2 md2 ->
    TC.op_begin_m Bw = Some (B4, tt) ->
    ((pc = LO_SUBR /\ TW.g_raw B4 <> 0 /\
      YK11.getr regs2 11 = w64 (lc_raw_w D (sv_c (lc_sub_kd D (lc_oc D c0)))) /\
      YK11.getr regs2 24 = w64 (p + TOP.fi_off (lc_raw_c4 D (sv_c (lc_sub_kd D (lc_oc D c0))))) /\
      YK11.getr regs2 23 = w64 (TOP.fi_n (lc_raw_c4 D (sv_c (lc_sub_kd D (lc_oc D c0))))) /\
      YK11.getr regs2 20 = w64 (F + 32) /\ YK11.getr regs2 22 = w64 1) \/
     (pc = LO_SUBT /\ TW.g_raw B4 = 0 /\
      YK11.getr regs2 25 = w64 (p + TOP.fi_off (sv_c (lc_sub_kd D (lc_oc D c0)))) /\
      YK11.getr regs2 22 = w64 (TOP.fi_n (sv_c (lc_sub_kd D (lc_oc D c0)))) /\
      YK11.getr regs2 20 = w64 1 /\
      rdword (rdv mem2) (sp1 + 24) = Some (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.S_queued Bw)))))) ->
    YK11.getr regs2 21 = Z_to_bv 64 (bv_swrap 32 (TW.S_queued Bw)) ->
    (forall r, acallee_saved r -> r <> 20 -> r <> 21 -> r <> 22 -> r <> 23 -> r <> 24 -> r <> 25 ->
       YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
    tw_at TMAP_B (rdv mem2) B4 ->
    garr8 segs (mrestrict (w_H W) mem2) (F + 32)
      (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display (lc_sub_kd D (lc_oc D c0)))
        (sv_key (lc_sub_kd D (lc_oc D c0))))) ->
    (forall i, 4 <= i < 8 -> rdv mem2 (SHF + i) = Some 0) ->
    (forall i, 0 <= i < 32 -> ~ (4 <= i < 8) -> rdv mem2 (SHF + i) = rdv mem (SHF + i)) ->
    (forall a, sp1 + 32 <= a <= sp0 -> rdv mem2 a = rdv mem a) ->
    (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m -> rdv mem2 (b + i) = rdv mem (b + i)) ->
    (forall a, F + 64 <= a < F + 256 -> rdv mem2 a = rdv mem a) ->
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
    SRr segs W (at_ pc regs2 mem2 md2) Q.

(* The display bit of a byte is a byte. *)
Lemma op_land1 : forall x, 0 <= x -> 0 <= Z.land x 1 < 256.
Proof.
intros x Hx. assert (E : Z.land x 1 = x mod 2) by exact (Z.land_ones x 1 ltac:(lia)).
rewrite E. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

Lemma op4_main : forall regs mem md (Bw : list byte) p n (D : list byte) (c0 : TOP.fuzz_in)
    (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 SHF -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 20 = w64 (F + 32) ->
  YK11.getr regs 25 = w64 (p + TOP.fi_off c0) -> YK11.getr regs 23 = w64 (TOP.fi_n c0) ->
  YK11.getr regs 24 = w64 (p + TOP.fi_off (lc_oc D c0)) -> YK11.getr regs 27 = w64 (TOP.fi_n (lc_oc D c0)) ->
  rdword (rdv mem) (sp1 + 112) = Some TB_g_s -> rdword (rdv mem) (sp1 + 168) = Some TB_M ->
  rdword (rdv mem) (sp1 + 184) = Some PG_GFN -> rdword (rdv mem) (sp1 + 104) = Some PG_RAW ->
  rdword (rdv mem) (sp1 + 144) = Some (F + 32) ->
  tw_at TMAP_B (rdv mem) Bw ->
  In (p, n) (ablocks B ly S) -> n = Z.of_nat (length D) -> n < 2 ^ 26 ->
  QF.fuzz_in_ok D c0 -> TOP.fi_n c0 <> 0 ->
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) D) ->
  op4_post regs mem Bw p D c0 Q ->
  SRr segs W (at_ O_ARM regs mem md) Q.
Proof using All.
intros regs mem md Bw p n D c0 Q HJ R2 R3 R4 R9 R18 R26 R20 R25 R23 R24 R27 H112 H168 H184 H104 H144 HTW Hin HnD Hn26
  HFI Hn0 HG8 HK.
destruct c0 as [off0 n0]. unfold QF.fuzz_in_ok in HFI. cbn [TOP.fi_off TOP.fi_n] in HFI, R25, R23, Hn0.
destruct HFI as (Hoff & Hnn & Hon). rewrite <- HnD in Hon.
unfold lc_oc in R24, R27. rewrite (op_u8 D off0 n0 Hn0) in R24, R27. cbn [fst TOP.fi_off TOP.fi_n] in R24, R27.
rewrite Z.add_assoc in R24.
unfold op4_post in HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
assert (HPT : alloc_ceiling <= PTRF) by (unfold PTRF; lia).
assert (EST : ESTACK = 4096) by reflexivity.
pose proof (req_size_pos n ltac:(lia)) as (Hq1 & Hq2).
pose proof (tw_len _ _ _ HTW) as HLB.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof (sep_block_frame segs B LAWS ly S W mem md p n LF_CID pos HAR0 Hin HFIN) as Hsep.
rewrite HFA in Hsep. change (fs_frame_bytes LF_CID) with 256 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
unfold in_app in Happ.
(* ---- run 1, the memset of OW ---- *)
pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 18144 4%nat TMAP_B_ok HTW
  TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as VQ.
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 18144) 4) as RQ.
change (TW.u_at Bw (TW.OFF_g_s + 18144) 4) with (TW.S_queued Bw) in VQ, RQ.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQ.
apply (op4_s1 regs mem md (TW.S_queued Bw) Q HJ R2 R3 R4 R9 R18 H112 VQ RQ).
intros regs1 mem1 md1 HJ1 Q21 Q22 KR1 ZS1 ZOW KA1 GA1.
set (B1 := TW.upd Bw TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW))).
assert (TW1 : tw_at TMAP_B (rdv mem1) B1).
{ pose proof (tw_fill_set TMAP_B (rdv mem) (rdv mem1) Bw TW.OFF_OW TB_OW TW.SZ_OW 0 0 304 TMAP_B_ok HTW TMAP_B_OW
    ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as T.
  rewrite !Z.add_0_r in T. refine (T _ _).
  - intros i Hi. rewrite (ZOW i Hi). reflexivity.
  - intros y Hy Hny. destruct (op_G_apart mem md HJ y (op_twin_G y Hy)) as (A0 & A1 & _ & _ & A4).
    exact (KA1 y A0 A1 Hny A4). }
(* ---- run 2, the memset of GOT ---- *)
apply (op4_s2 regs1 mem1 md1 Q HJ1
  (eq_trans (KR1 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R2)
  (eq_trans (KR1 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R3)
  (eq_trans (KR1 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R4)).
intros regs2 mem2 md2 HJ2 KR2 ZGOT KA2 GA2.
set (B2 := TW.upd B1 TW.OFF_GOT (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT))).
assert (TW2 : tw_at TMAP_B (rdv mem2) B2).
{ pose proof (tw_fill_set TMAP_B (rdv mem1) (rdv mem2) B1 TW.OFF_GOT TB_GOT TW.SZ_GOT 0 0 224 TMAP_B_ok TW1 TMAP_B_GOT
    ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as T.
  rewrite !Z.add_0_r in T. refine (T _ _).
  - intros i Hi. rewrite (ZGOT i Hi). reflexivity.
  - intros y Hy Hny. destruct (op_G_apart mem md HJ y (op_twin_G y Hy)) as (A0 & _ & _ & _ & A4).
    exact (KA2 y A0 Hny A4). }
pose proof (tw_len _ _ _ TW2) as LB2.
assert (KR12 : forall r, acallee_saved r -> r <> 21 -> r <> 22 ->
  YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr H21 H22; exact (eq_trans (KR2 r Hr) (KR1 r Hr H21 H22))).
assert (K02 : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (SHF + 4 <= a < SHF + 8) ->
  ~ (sp1 - ESTACK <= a < sp1) -> rdv mem2 a = rdv mem a).
{ intros a A0 A1 A2 A4. rewrite (KA2 a A0 (fun Hc => A1 (op_inG_GOT a Hc)) A4).
  exact (KA1 a A0 A2 (fun Hc => A1 (op_inG_OW a Hc)) A4). }
assert (ZS2 : forall i, 4 <= i < 8 -> rdv mem2 (SHF + i) = Some 0).
{ intros i Hi. destruct (op_SH_apart mem md HJ i ltac:(lia)) as (A0 & A1 & _ & _ & A4).
  rewrite (KA2 _ A0 (fun Hc => A1 (op_inG_GOT _ Hc)) A4). exact (ZS1 i Hi). }
(* ---- run 3: g_fail_next, OW.desk_off, M.fail, the memset of c ---- *)
pose proof (tw_read_val segs (mrestrict (w_H W) mem2) TMAP_B B2 TW.OFF_g_fail_next TB_g_fail_next 1 0 1%nat TMAP_B_ok
  TW2 TMAP_B_g_fail_next ltac:(lia) ltac:(lia)) as VG.
rewrite !Z.add_0_r in VG.
pose proof (TWL.u_at_range B2 TW.OFF_g_fail_next 1) as RG. change (2 ^ (8 * Z.of_nat 1)) with 256 in RG.
set (gfn := TW.u_at B2 TW.OFF_g_fail_next 1) in VG, RG.
assert (SP2 : forall a, sp1 <= a <= sp0 -> rdv mem2 a = rdv mem a).
{ intros a Ha. destruct (op_stk_apart a Ha) as (A0 & A1 & A2 & _ & A4). exact (K02 a A0 A1 A2 A4). }
apply (op4_s3 regs2 mem2 md2 gfn Q HJ2
  (eq_trans (KR12 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R2)
  (eq_trans (KR12 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R3)
  (eq_trans (KR12 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R4)
  (eq_trans (KR12 9 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R9)
  (eq_trans (KR12 20 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R20)
  (eq_trans (KR2 22 ltac:(unfold acallee_saved; lia)) Q22) VG RG
  (op_rdw_kept mem mem2 (sp1 + 184) PG_GFN (fun k0 Hk => SP2 (sp1 + 184 + k0) ltac:(lia)) H184)
  (op_rdw_kept mem mem2 (sp1 + 168) TB_M (fun k0 Hk => SP2 (sp1 + 168 + k0) ltac:(lia)) H168) ZS2).
intros regs3 mem3 md3 HJ3 KR3 VOW3 VM3 ZC3 KA3 GA3.
(* the world after op_begin *)
set (B3 := TW.set_OW_desk_off B2 (-1)).
set (B4 := TW.set_M_fail B3 (TW.g_fail_next B3)).
assert (EG3 : TW.g_fail_next B3 = gfn).
{ unfold B3, TW.set_OW_desk_off, TW.g_fail_next, gfn. apply TWL.u_at_upd_out.
  - unfold TW.A_OW_desk_off, TW.OFF_OW. lia.
  - unfold TW.OFF_g_fail_next. lia.
  - left. unfold TW.OFF_g_fail_next, TW.A_OW_desk_off, TW.OFF_OW. cbn [Z.of_nat]. lia.
  - rewrite TWL.length_put, LB2. change (Z.of_nat (Z.to_nat TW.W_LEN)) with 65616. unfold TW.A_OW_desk_off, TW.OFF_OW.
    cbn [Z.of_nat]. lia. }
set (rdm := fun y => if (TB_M + 88 <=? y) && (y <? TB_M + 92) then rdv mem2 y else rdv mem3 y).
assert (RM1 : forall y, ~ (TB_M + 88 <= y < TB_M + 92) -> rdm y = rdv mem3 y).
{ intros y Hy. unfold rdm. destruct (Z.leb_spec (TB_M + 88) y); destruct (Z.ltb_spec y (TB_M + 92));
    cbn [andb]; first [reflexivity | lia]. }
assert (RM2 : forall y, TB_M + 88 <= y < TB_M + 92 -> rdm y = rdv mem2 y).
{ intros y Hy. unfold rdm. destruct (Z.leb_spec (TB_M + 88) y); destruct (Z.ltb_spec y (TB_M + 92));
    cbn [andb]; first [reflexivity | lia]. }
assert (TWa : tw_at TMAP_B rdm B3).
{ pose proof (tw_write TMAP_B (rdv mem2) rdm B2 TW.OFF_OW TB_OW TW.SZ_OW 232 4 (-1) TMAP_B_ok TW2 TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat]; lia)) as T.
  refine (T _ _).
  - intros j Hj. rewrite RM1 by (unfold TB_OW, TB_M; lia).
    assert (EL : YO0f.le_byte 4294967295 4 j = YO0f.le_byte (-1) 4 j).
    { assert (Hj' : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat) by lia.
      destruct Hj' as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. }
    exact (eq_trans (VOW3 j Hj) (f_equal Some EL)).
  - intros y Hy Hny. destruct (Z.leb_spec (TB_M + 88) y) as [Hm1 | Hm1];
      [destruct (Z.ltb_spec y (TB_M + 92)) as [Hm2 | Hm2]|].
    + exact (RM2 y (conj Hm1 Hm2)).
    + rewrite (RM1 y ltac:(lia)).
      destruct (op_G_apart mem md HJ y (op_twin_G y Hy)) as (A0 & _ & A2 & _ & A4).
      exact (KA3 y A0 ltac:(cbn [Z.of_nat] in Hny; lia) ltac:(lia) A2 A4).
    + rewrite (RM1 y ltac:(lia)).
      destruct (op_G_apart mem md HJ y (op_twin_G y Hy)) as (A0 & _ & A2 & _ & A4).
      exact (KA3 y A0 ltac:(cbn [Z.of_nat] in Hny; lia) ltac:(lia) A2 A4). }
assert (TW3 : tw_at TMAP_B (rdv mem3) B4).
{ pose proof (tw_write TMAP_B rdm (rdv mem3) B3 TW.OFF_M TB_M TW.SZ_M 88 4 gfn TMAP_B_ok TWa TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_nat]; lia)) as T.
  unfold B4. rewrite EG3. refine (T _ _).
  - intros j Hj. exact (VM3 j Hj).
  - intros y Hy Hny. symmetry. apply RM1. cbn [Z.of_nat] in Hny. lia. }
assert (EOB : TC.op_begin_m Bw = Some (B4, tt)) by reflexivity.
clearbody B4.
assert (KR123 : forall r, acallee_saved r -> r <> 21 -> r <> 22 ->
  YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr H21 H22; exact (eq_trans (KR3 r Hr) (KR12 r Hr H21 H22))).
assert (K03 : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (SHF + 4 <= a < SHF + 8) ->
  ~ (F + 32 <= a < F + 64) -> ~ (sp1 - ESTACK <= a < sp1) -> rdv mem3 a = rdv mem a).
{ intros a A0 A1 A2 A3 A4.
  rewrite (KA3 a A0 (fun Hc => A1 (op_inG_OW a ltac:(lia))) (fun Hc => A1 (op_inG_M a Hc)) A3 A4).
  exact (K02 a A0 A1 A2 A4). }
assert (ZS3 : forall i, 4 <= i < 8 -> rdv mem3 (SHF + i) = Some 0).
{ intros i Hi. destruct (op_SH_apart mem md HJ i ltac:(lia)) as (A0 & A1 & A2 & _ & A4).
  rewrite (KA3 _ A0 (fun Hc => A1 (op_inG_OW (SHF + i) ltac:(lia))) (fun Hc => A1 (op_inG_M _ Hc)) A2 A4).
  exact (ZS2 i Hi). }
assert (SP3 : forall a, sp1 <= a <= sp0 -> rdv mem3 a = rdv mem a).
{ intros a Ha. destruct (op_stk_apart a Ha) as (A0 & A1 & A2 & A3 & A4). exact (K03 a A0 A1 A2 A3 A4). }
assert (HG83 : garr8 segs (mrestrict (w_H W) mem3) p (map (fun b : byte => bv_unsigned b) D)).
{ apply (lc_garr8_kept (w_H W) (w_H W) mem mem3 p _); [|exact HG8].
  intros j Hj. rewrite length_map, <- HnD in Hj.
  destruct (op_blk_apart mem md p n HJ Hin j ltac:(lia)) as (A0 & A1 & A2 & A3 & _ & A5).
  exact (K03 _ A0 A1 A2 A3 A5). }
assert (R3_21 : YK11.getr regs3 21 = Z_to_bv 64 (bv_swrap 32 (TW.S_queued Bw)))
  by exact (eq_trans (KR3 21 ltac:(unfold acallee_saved; lia)) (eq_trans (KR2 21 ltac:(unfold acallee_saved; lia)) Q21)).
assert (RK : forall r v, acallee_saved r -> r <> 21 -> r <> 22 -> YK11.getr regs (Z_to_bv 5 r) = v ->
  YK11.getr regs3 (Z_to_bv 5 r) = v) by (intros r v Hr H21 H22 Hv; rewrite (KR123 r Hr H21 H22); exact Hv).
pose proof (RK 9 _ ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) R9) as R3_9.
pose proof (RK 20 _ ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) R20) as R3_20.
pose proof (RK 23 _ ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) R23) as R3_23.
pose proof (RK 24 _ ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) R24) as R3_24.
pose proof (RK 25 _ ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) R25) as R3_25.
pose proof (RK 26 _ ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) R26) as R3_26.
pose proof (RK 27 _ ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) R27) as R3_27.
pose proof (op_rdw_kept mem mem3 (sp1 + 104) PG_RAW (fun k0 Hk => SP3 (sp1 + 104 + k0) ltac:(lia)) H104) as H104_3.
pose proof (op_rdw_kept mem mem3 (sp1 + 144) (F + 32) (fun k0 Hk => SP3 (sp1 + 144 + k0) ltac:(lia)) H144) as H144_3.
pose proof (TWL.u_at_range B4 TW.OFF_g_raw 4) as RR. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RR.
set (graw := TW.u_at B4 TW.OFF_g_raw 4) in RR.
(* what the K stage's memory keeps of run 3's *)
assert (KF : forall regsK memK mdK, J memK mdK ->
  (forall r, acallee_saved r -> r <> 22 -> r <> 23 -> r <> 24 ->
     YK11.getr regsK (Z_to_bv 5 r) = YK11.getr regs3 (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdv memK a = rdv mem3 a) ->
  YK11.getr regsK 9 = w64 sp1 /\ YK11.getr regsK 20 = w64 (F + 32) /\ YK11.getr regsK 26 = w64 SHADOW_OFF /\
  rdword (rdv memK) (sp1 + 104) = Some PG_RAW /\ rdword (rdv memK) (sp1 + 144) = Some (F + 32) /\
  val_mem segs (mrestrict (w_H W) memK) TB_g_raw 4 graw /\
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) memK a) /\
  (forall a, F + 57 <= a < F + 64 -> apresent (w_H W) memK a) /\
  (forall i, 4 <= i < 8 -> rdv memK (SHF + i) = Some 0) /\
  (forall a kk, p <= a -> a + kk <= p + req_size n -> range_addressable (rdv memK) SHADOW_OFF a kk)).
{ intros regsK memK mdK HJK KRK KMK.
  assert (TWK : tw_at TMAP_B (rdv memK) B4).
  { apply (tw_kept TMAP_B (rdv mem3) (rdv memK) B4 TW3). intros y Hy.
    destruct (op_G_apart mem md HJ y (op_twin_G y Hy)) as (A0 & _ & _ & _ & _). exact (KMK y A0). }
  split; [exact (eq_trans (KRK 9 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) R3_9)|].
  split; [exact (eq_trans (KRK 20 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) R3_20)|].
  split; [exact (eq_trans (KRK 26 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) R3_26)|].
  split; [exact (op_rdw_kept mem3 memK (sp1 + 104) PG_RAW (fun k0 Hk => KMK (sp1 + 104 + k0) ltac:(lia)) H104_3)|].
  split; [exact (op_rdw_kept mem3 memK (sp1 + 144) (F + 32) (fun k0 Hk => KMK (sp1 + 144 + k0) ltac:(lia)) H144_3)|].
  split.
  { pose proof (tw_read_val segs (mrestrict (w_H W) memK) TMAP_B B4 TW.OFF_g_raw TB_g_raw TW.SZ_g_raw 0 4%nat TMAP_B_ok
      TWK TMAP_B_g_raw ltac:(lia) ltac:(unfold TW.SZ_g_raw; lia)) as VR.
    rewrite !Z.add_0_r in VR. exact VR. }
  split; [intros a Ha; apply (op_stack_pres memK mdK HJK); lia|].
  split; [intros a Ha; destruct (op_frame_pres memK mdK HJK) as (HFb & _ & _); apply HFb; lia|].
  split.
  { intros i Hi. rewrite (KMK (SHF + i)) by (unfold SHADOW_OFF in *; lia). exact (ZS3 i Hi). }
  intros a kk H1 H2. apply (range_addressable_of_block segs B LAWS ly S W memK mdK p n);
    [exact (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJK) | exact Hin | exact H1 | exact H2]. }
(* ---- from stage D's post to the cut ---- *)
assert (DTAIL : forall regsK memK mdK kv av s7v s8v,
  J memK mdK ->
  YK11.getr regsK 11 = w64 kv -> YK11.getr regsK 12 = w64 av -> YK11.getr regsK 22 = w64 1 ->
  YK11.getr regsK 23 = w64 s7v -> YK11.getr regsK 24 = w64 s8v ->
  (forall r, acallee_saved r -> r <> 22 -> r <> 23 -> r <> 24 ->
     YK11.getr regsK (Z_to_bv 5 r) = YK11.getr regs3 (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdv memK a = rdv mem3 a) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) memK a) ->
  forall disp wv curR nR curT nT c3,
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 n0)) = mkLsv (DSpec.KEY (kv mod 9 + 1) av) disp c3 ->
  0 <= disp < 256 ->
  lc_raw_w D c3 = wv -> p + TOP.fi_off (lc_raw_c4 D c3) = curR -> TOP.fi_n (lc_raw_c4 D c3) = nR ->
  p + TOP.fi_off c3 = curT -> TOP.fi_n c3 = nT ->
  d_post regsK memK graw disp (DSpec.KEY (kv mod 9 + 1) av) wv curR nR curT nT Q).
{ intros regsK memK mdK kv av s7v s8v HJK K11 K12 K22 K23 K24 KRK KMK GAK disp wv curR nR curT nT c3 EKD Hd Ew EcR EnR
    EcT EnT.
  rewrite EKD in HK. cbn [sv_c sv_key sv_display] in HK.
  intros regs4 mem4 md4 pc HJ4 Hbr KR4 VD4 VK4 KA4 GA4.
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 24 <= a < sp1 + 32) ->
    rdv mem4 a = rdv mem3 a) by (intros a Ha H1 H2 H3; rewrite (KA4 a Ha H1 H2 H3); exact (KMK a Ha)).
  assert (RK21 : YK11.getr regsK 21 = Z_to_bv 64 (bv_swrap 32 (TW.S_queued Bw)))
    by exact (eq_trans (KRK 21 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) R3_21).
  apply (HK regs4 mem4 md4 pc B4 HJ4 EOB).
  - destruct (op_swrap_z graw RR) as (_ & S2). change (TW.g_raw B4) with (bv_swrap 32 graw).
    destruct Hbr as [(-> & Hg & B11 & B24 & B23 & B20 & B22) | (-> & Hg & B25 & B22 & B20 & B24w)].
    + left. split; [reflexivity|]. split; [intros Hz; exact (Hg (proj1 S2 Hz))|].
      rewrite Ew, EcR, EnR. exact (conj B11 (conj B24 (conj B23 (conj B20 B22)))).
    + right. split; [reflexivity|]. split; [exact (proj2 S2 Hg)|].
      rewrite EcT, EnT. split; [exact B25|]. split; [exact B22|]. split; [exact B20|].
      rewrite B24w, RK21. reflexivity.
  - exact (eq_trans (KR4 21 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      RK21).
  - intros r Hr H20 H21 H22 H23 H24 H25. rewrite (KR4 r Hr H20 H22 H23 H24 H25), (KRK r Hr H22 H23 H24).
    exact (KR123 r Hr H21 H22).
  - apply (tw_kept TMAP_B (rdv mem3) (rdv mem4) B4 TW3). intros y Hy.
    destruct (op_G_apart mem md HJ y (op_twin_G y Hy)) as (A0 & _ & A2 & A3 & _).
    apply K4; [exact A0 | lia | lia | exact A3].
  - apply (op_c_garr8 mem4 disp _ Hd). intros j Hj.
    destruct (Nat.eqb_spec j 25) as [-> | Hj25].
    + replace (F + 32 + Z.of_nat 25) with (F + 57) by (cbn [Z.of_nat]; lia). exact VD4.
    + destruct (Nat.ltb_spec j 28) as [Hj28 | Hj28].
      * rewrite (K4 (F + 32 + Z.of_nat j) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        exact (ZC3 (Z.of_nat j) ltac:(lia)).
      * replace (F + 32 + Z.of_nat j) with (F + 60 + Z.of_nat (j - 28)) by lia. exact (VK4 (j - 28)%nat ltac:(lia)).
  - intros i Hi. destruct (op_SH_apart mem md HJ i ltac:(lia)) as (A0 & _ & A2 & A3 & _).
    rewrite (K4 _ A0 ltac:(lia) ltac:(lia) A3). exact (ZS3 i Hi).
  - intros i Hi Hn. destruct (op_SH_apart mem md HJ i Hi) as (A0 & A1 & A2 & A3 & A4).
    rewrite (K4 _ A0 ltac:(lia) ltac:(lia) A3). exact (K03 _ A0 A1 ltac:(lia) A2 A4).
  - intros a Ha. destruct (op_stk_apart a ltac:(lia)) as (A0 & A1 & A2 & A3 & A4).
    rewrite (K4 a A0 ltac:(lia) ltac:(lia) ltac:(lia)). exact (K03 a A0 A1 A2 A3 A4).
  - intros b m i Hbm Hi. destruct (op_blk_apart mem md b m HJ Hbm i Hi) as (A0 & A1 & A2 & A3 & A4 & A5).
    rewrite (K4 _ A0 ltac:(lia) ltac:(lia) A4). exact (K03 _ A0 A1 A2 A3 A5).
  - intros a Ha. destruct (op_ftail_apart mem md a HJ Ha) as (A0 & A1 & A2 & A3 & A4 & A5).
    rewrite (K4 _ A0 ltac:(lia) ltac:(lia) A4). exact (K03 _ A0 A1 A2 A3 A5).
  - intros a Ha. exact (GA4 a (GAK a (GA3 a (GA2 a (GA1 a Ha))))). }
(* ---- the bytes after the op byte ---- *)
assert (HjD : forall kk, 1 <= kk -> kk < n0 -> (Z.to_nat (off0 + kk) < length D)%nat) by (intros kk H1 H2; lia).
assert (VB : forall kk, 1 <= kk -> kk < n0 ->
  val_mem segs (mrestrict (w_H W) mem3) (p + off0 + kk) 1 (DSpec.at8 D (Z.to_nat (off0 + kk))) /\
  0 <= DSpec.at8 D (Z.to_nat (off0 + kk)) < 256).
{ intros kk H1 H2. destruct (op_g8 mem3 p D (Z.to_nat (off0 + kk)) HG83 (HjD kk H1 H2)) as (V & Bd).
  rewrite Z2Nat.id in V by lia. rewrite Z.add_assoc in V. exact (conj V Bd). }
assert (HRA3 : forall a kk, p <= a -> a + kk <= p + req_size n ->
  range_addressable (rdv mem3) SHADOW_OFF a kk).
{ intros a kk H1 H2. apply (range_addressable_of_block segs B LAWS ly S W mem3 md3 p n);
    [exact (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) | exact Hin | exact H1 | exact H2]. }
assert (Hcase : n0 = 1 \/ n0 = 2 \/ n0 = 3 \/ n0 = 4 \/ n0 = 5 \/ 6 <= n0) by lia.
destruct Hcase as [-> | [-> | [-> | [-> | [-> | H6]]]]].
- (* one byte left before the op byte *)
  apply (op4_k1 regs3 mem3 md3 (p + off0 + 1) Q HJ3 R3_27 R3_24 ltac:(lia)).
  intros regsK memK mdK HJK K11 K12 K22 K23 K24 KRK KMK GAK.
  destruct (KF regsK memK mdK HJK KRK KMK) as (K9 & K20 & K26 & K104 & K144 & KVR & KPs & KPc & _ & _).
  apply (op4_d0 regsK memK mdK (p + off0 + 1) graw 0 0 Q HJK K9 K20 K11 K12 K24 K26 K22 K23 ltac:(lia) ltac:(lia)
    ltac:(lia) K104 K144 KVR RR KPs KPc).
  exact (DTAIL regsK memK mdK 0 0 0 (p + off0 + 1) HJK K11 K12 K22 K23 K24 KRK KMK GAK 0 0 (p + off0 + 1) 0
    (p + off0 + 1) 0 (TOP.FuzzIn (off0 + 1) 0) (op_kd1 D off0) ltac:(lia) eq_refl
    ltac:(rewrite (proj2 (op_raw0 D _)); cbn [TOP.fi_off]; lia) eq_refl ltac:(cbn [TOP.fi_off]; lia) eq_refl).
- (* two bytes left: the kind byte *)
  destruct (VB 1 ltac:(lia) ltac:(lia)) as (Vkb & Bkb).
  destruct (HRA3 (p + off0 + 1) 1 ltac:(lia) ltac:(lia) (p + off0 + 1) ltac:(lia)) as (sb & HSB & Hsbr).
  unfold shadow_of_addr, saddr_ok in HSB, Hsbr.
  apply (op4_k2 regs3 mem3 md3 (p + off0 + 1) _ sb Q HJ3 R3_24
    ltac:(replace (p + off0 + 1 - 1) with (p + off0) by lia; exact R3_25) R3_26 R3_23 R3_27 ltac:(lia)
    ltac:(unfold PTRF; lia) ltac:(lia) Vkb Bkb HSB
    ltac:(destruct Hsbr as [Hz | (H1 & H2)]; [left; exact Hz | right; lia])).
  intros regsK memK mdK HJK K11 K12 K22 K23 K24 KRK KMK GAK.
  destruct (KF regsK memK mdK HJK KRK KMK) as (K9 & K20 & K26 & K104 & K144 & KVR & KPs & KPc & _ & _).
  apply (op4_d0 regsK memK mdK (p + off0 + 1 + 1) graw _ 0 Q HJK K9 K20 K11 K12 K24 K26 K22 K23 Bkb ltac:(lia)
    ltac:(lia) K104 K144 KVR RR KPs KPc).
  exact (DTAIL regsK memK mdK _ 0 0 (p + off0 + 1 + 1) HJK K11 K12 K22 K23 K24 KRK KMK GAK 0 0 (p + off0 + 1 + 1) 0
    (p + off0 + 1 + 1) 0 (TOP.FuzzIn (off0 + 2) 0) (op_kd2 D off0) ltac:(lia) eq_refl
    ltac:(rewrite (proj2 (op_raw0 D _)); cbn [TOP.fi_off]; lia) eq_refl ltac:(cbn [TOP.fi_off]; lia) eq_refl).
- (* three bytes left: the kind and address bytes *)
  destruct (VB 1 ltac:(lia) ltac:(lia)) as (Vkb & Bkb). destruct (VB 2 ltac:(lia) ltac:(lia)) as (Vab & Bab).
  destruct (HRA3 (p + off0 + 1) 1 ltac:(lia) ltac:(lia) (p + off0 + 1) ltac:(lia)) as (sb & HSB & Hsbr).
  unfold shadow_of_addr, saddr_ok in HSB, Hsbr.
  apply (op4_k3 regs3 mem3 md3 (p + off0 + 1) 3 _ sb _ Q HJ3 R3_24
    ltac:(replace (p + off0 + 1 - 1) with (p + off0) by lia; exact R3_25) R3_26 R3_23 R3_27 ltac:(lia) ltac:(lia)
    ltac:(unfold PTRF; lia) ltac:(lia)
    Vkb Bkb HSB ltac:(destruct Hsbr as [Hz | (H1 & H2)]; [left; exact Hz | right; lia])
    ltac:(replace (p + off0 + 1 + 1) with (p + off0 + 2) by lia; exact Vab) Bab
    (HRA3 (p + off0 + 1 + 1) 1 ltac:(lia) ltac:(lia))).
  intros regsK memK mdK HJK K11 K12 K22 K23 K24 KRK KMK GAK.
  destruct (KF regsK memK mdK HJK KRK KMK) as (K9 & K20 & K26 & K104 & K144 & KVR & KPs & KPc & _ & _).
  apply (op4_d0 regsK memK mdK (p + off0 + 1 + 2) graw _ _ Q HJK K9 K20 K11 K12 K24 K26 K22 K23 Bkb Bab
    ltac:(lia) K104 K144 KVR RR KPs KPc).
  exact (DTAIL regsK memK mdK _ _ _ (p + off0 + 1 + 2) HJK K11 K12 K22 K23 K24 KRK KMK GAK 0 0 (p + off0 + 1 + 2) 0
    (p + off0 + 1 + 2) 0 (TOP.FuzzIn (off0 + 3) 0) (op_kd3 D off0) ltac:(lia) eq_refl
    ltac:(rewrite (proj2 (op_raw0 D _)); cbn [TOP.fi_off]; lia) eq_refl ltac:(cbn [TOP.fi_off]; lia) eq_refl).
- (* four bytes left: the display byte *)
  destruct (VB 1 ltac:(lia) ltac:(lia)) as (Vkb & Bkb). destruct (VB 2 ltac:(lia) ltac:(lia)) as (Vab & Bab).
  destruct (VB 3 ltac:(lia) ltac:(lia)) as (Vdb & Bdb).
  destruct (HRA3 (p + off0 + 1) 1 ltac:(lia) ltac:(lia) (p + off0 + 1) ltac:(lia)) as (sb & HSB & Hsbr).
  unfold shadow_of_addr, saddr_ok in HSB, Hsbr.
  apply (op4_k3 regs3 mem3 md3 (p + off0 + 1) 4 _ sb _ Q HJ3 R3_24
    ltac:(replace (p + off0 + 1 - 1) with (p + off0) by lia; exact R3_25) R3_26 R3_23 R3_27 ltac:(lia) ltac:(lia)
    ltac:(unfold PTRF; lia) ltac:(lia)
    Vkb Bkb HSB ltac:(destruct Hsbr as [Hz | (H1 & H2)]; [left; exact Hz | right; lia])
    ltac:(replace (p + off0 + 1 + 1) with (p + off0 + 2) by lia; exact Vab) Bab
    (HRA3 (p + off0 + 1 + 1) 1 ltac:(lia) ltac:(lia))).
  intros regsK memK mdK HJK K11 K12 K22 K23 K24 KRK KMK GAK.
  destruct (KF regsK memK mdK HJK KRK KMK) as (K9 & K20 & K26 & K104 & K144 & KVR & KPs & KPc & KZS & KRA).
  assert (KVdb : val_mem segs (mrestrict (w_H W) memK) (p + off0 + 1 + 2) 1 (DSpec.at8 D (Z.to_nat (off0 + 3)))).
  { replace (p + off0 + 1 + 2) with (p + off0 + 3) by lia.
    apply (YE36.val_mem1_of_aview (w_H W) memK). rewrite (KMK (p + off0 + 3) ltac:(lia)).
    exact (TransportGNoticeB.aview_of_val_mem1 (w_H W) mem3 _ _ Vdb Bdb). }
  apply (op4_d1 regsK memK mdK (p + off0 + 1 + 2) graw _ _ _ Q HJK K9 K20 K11 K12 K24 K26 K22 K23 Bkb Bab
    ltac:(lia) ltac:(unfold PTRF; lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (op_blk_raw mem md p n (p + off0 + 1 + 2) 1 HJ Hin ltac:(lia) ltac:(lia) ltac:(lia))
    K104 K144 KVR RR KPs KPc KZS KVdb Bdb (KRA (p + off0 + 1 + 2) 1 ltac:(lia) ltac:(lia))).
  pose proof (op_kd4 D off0 4 ltac:(lia)) as EKD.
  pose proof (op_land1 (DSpec.at8 D (Z.to_nat (off0 + 3)))
    ltac:(pose proof (DSpec.at8_range D (Z.to_nat (off0 + 3))); lia)) as Hd.
  exact (DTAIL regsK memK mdK _ _ _ (p + off0 + 1 + 2) HJK K11 K12 K22 K23 K24 KRK KMK GAK _ 0 (p + off0 + 1 + 2 + 1) 0
    (p + off0 + 1 + 2 + 1) 0 (TOP.FuzzIn (off0 + 4) 0) EKD Hd eq_refl
    ltac:(rewrite (proj2 (op_raw0 D _)); cbn [TOP.fi_off]; lia) eq_refl ltac:(cbn [TOP.fi_off]; lia) eq_refl).
- (* five bytes left: the display byte and the length word's low byte *)
  destruct (VB 1 ltac:(lia) ltac:(lia)) as (Vkb & Bkb). destruct (VB 2 ltac:(lia) ltac:(lia)) as (Vab & Bab).
  destruct (VB 3 ltac:(lia) ltac:(lia)) as (Vdb & Bdb). destruct (VB 4 ltac:(lia) ltac:(lia)) as (Vlo & Blo).
  destruct (HRA3 (p + off0 + 1) 1 ltac:(lia) ltac:(lia) (p + off0 + 1) ltac:(lia)) as (sb & HSB & Hsbr).
  unfold shadow_of_addr, saddr_ok in HSB, Hsbr.
  apply (op4_k3 regs3 mem3 md3 (p + off0 + 1) 5 _ sb _ Q HJ3 R3_24
    ltac:(replace (p + off0 + 1 - 1) with (p + off0) by lia; exact R3_25) R3_26 R3_23 R3_27 ltac:(lia) ltac:(lia)
    ltac:(unfold PTRF; lia) ltac:(lia)
    Vkb Bkb HSB ltac:(destruct Hsbr as [Hz | (H1 & H2)]; [left; exact Hz | right; lia])
    ltac:(replace (p + off0 + 1 + 1) with (p + off0 + 2) by lia; exact Vab) Bab
    (HRA3 (p + off0 + 1 + 1) 1 ltac:(lia) ltac:(lia))).
  intros regsK memK mdK HJK K11 K12 K22 K23 K24 KRK KMK GAK.
  destruct (KF regsK memK mdK HJK KRK KMK) as (K9 & K20 & K26 & K104 & K144 & KVR & KPs & KPc & KZS & KRA).
  assert (KV : forall kk v, 1 <= kk < 5 -> 0 <= v < 256 ->
    val_mem segs (mrestrict (w_H W) mem3) (p + off0 + kk) 1 v ->
    val_mem segs (mrestrict (w_H W) memK) (p + off0 + kk) 1 v).
  { intros kk v Hkk Hv V. apply (YE36.val_mem1_of_aview (w_H W) memK).
    pose proof (TransportGNoticeB.aview_of_val_mem1 (w_H W) mem3 _ _ V Hv) as A.
    rewrite (KMK (p + off0 + kk) ltac:(lia)). exact A. }
  apply (op4_d2 regsK memK mdK (p + off0 + 1 + 2) graw _ _ _ _ Q HJK K9 K20 K11 K12 K24 K26 K22 K23 Bkb Bab
    ltac:(lia) ltac:(unfold PTRF; lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (op_blk_raw mem md p n (p + off0 + 1 + 2) 2 HJ Hin ltac:(lia) ltac:(lia) ltac:(lia))
    K104 K144 KVR RR KPs KPc KZS
    ltac:(replace (p + off0 + 1 + 2) with (p + off0 + 3) by lia; exact (KV 3 _ ltac:(lia) Bdb Vdb)) Bdb
    ltac:(replace (p + off0 + 1 + 2 + 1) with (p + off0 + 4) by lia; exact (KV 4 _ ltac:(lia) Blo Vlo)) Blo
    (KRA (p + off0 + 1 + 2) 2 ltac:(lia) ltac:(lia))).
  pose proof (op_kd4 D off0 5 ltac:(lia)) as EKD.
  pose proof (op_land1 (DSpec.at8 D (Z.to_nat (off0 + 3)))
    ltac:(pose proof (DSpec.at8_range D (Z.to_nat (off0 + 3))); lia)) as Hd.
  destruct (op_raw1 D (off0 + 4)) as (EW & EC).
  exact (DTAIL regsK memK mdK _ _ _ (p + off0 + 1 + 2) HJK K11 K12 K22 K23 K24 KRK KMK GAK _ _ (p + off0 + 1 + 2 + 2) 0
    (p + off0 + 1 + 2 + 1) 1 (TOP.FuzzIn (off0 + 4) 1) EKD Hd EW ltac:(rewrite EC; cbn [TOP.fi_off]; lia)
    ltac:(rewrite EC; reflexivity) ltac:(cbn [TOP.fi_off]; lia) eq_refl).
- (* six or more bytes left: the display byte and the length word *)
  destruct (VB 1 ltac:(lia) ltac:(lia)) as (Vkb & Bkb). destruct (VB 2 ltac:(lia) ltac:(lia)) as (Vab & Bab).
  destruct (VB 3 ltac:(lia) ltac:(lia)) as (Vdb & Bdb). destruct (VB 4 ltac:(lia) ltac:(lia)) as (Vlo & Blo).
  destruct (VB 5 ltac:(lia) ltac:(lia)) as (Vhi & Bhi).
  destruct (HRA3 (p + off0 + 1) 1 ltac:(lia) ltac:(lia) (p + off0 + 1) ltac:(lia)) as (sb & HSB & Hsbr).
  unfold shadow_of_addr, saddr_ok in HSB, Hsbr.
  apply (op4_k3 regs3 mem3 md3 (p + off0 + 1) n0 _ sb _ Q HJ3 R3_24
    ltac:(replace (p + off0 + 1 - 1) with (p + off0) by lia; exact R3_25) R3_26 R3_23 R3_27 ltac:(lia) ltac:(lia)
    ltac:(unfold PTRF; lia) ltac:(lia)
    Vkb Bkb HSB ltac:(destruct Hsbr as [Hz | (H1 & H2)]; [left; exact Hz | right; lia])
    ltac:(replace (p + off0 + 1 + 1) with (p + off0 + 2) by lia; exact Vab) Bab
    (HRA3 (p + off0 + 1 + 1) 1 ltac:(lia) ltac:(lia))).
  intros regsK memK mdK HJK K11 K12 K22 K23 K24 KRK KMK GAK.
  destruct (KF regsK memK mdK HJK KRK KMK) as (K9 & K20 & K26 & K104 & K144 & KVR & KPs & KPc & KZS & KRA).
  assert (KV : forall kk v, 1 <= kk < n0 -> 0 <= v < 256 ->
    val_mem segs (mrestrict (w_H W) mem3) (p + off0 + kk) 1 v ->
    val_mem segs (mrestrict (w_H W) memK) (p + off0 + kk) 1 v).
  { intros kk v Hkk Hv V. apply (YE36.val_mem1_of_aview (w_H W) memK).
    pose proof (TransportGNoticeB.aview_of_val_mem1 (w_H W) mem3 _ _ V Hv) as A.
    rewrite (KMK (p + off0 + kk) ltac:(lia)). exact A. }
  apply (op4_d3 regsK memK mdK (p + off0 + 1 + 2) (n0 - 3) graw _ _ _ _ _ Q HJK K9 K20 K11 K12 K24 K26 K22 K23
    ltac:(lia) Bkb Bab ltac:(lia) ltac:(unfold PTRF; lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (op_blk_raw mem md p n (p + off0 + 1 + 2) 3 HJ Hin ltac:(lia) ltac:(lia) ltac:(lia))
    K104 K144 KVR RR KPs KPc KZS
    ltac:(replace (p + off0 + 1 + 2) with (p + off0 + 3) by lia; exact (KV 3 _ ltac:(lia) Bdb Vdb)) Bdb
    ltac:(replace (p + off0 + 1 + 2 + 1) with (p + off0 + 4) by lia; exact (KV 4 _ ltac:(lia) Blo Vlo)) Blo
    ltac:(replace (p + off0 + 1 + 2 + 2) with (p + off0 + 5) by lia; exact (KV 5 _ ltac:(lia) Bhi Vhi)) Bhi
    (KRA (p + off0 + 1 + 2) 3 ltac:(lia) ltac:(lia))).
  pose proof (op_kd4 D off0 n0 ltac:(lia)) as EKD.
  pose proof (op_land1 (DSpec.at8 D (Z.to_nat (off0 + 3)))
    ltac:(pose proof (DSpec.at8_range D (Z.to_nat (off0 + 3))); lia)) as Hd.
  destruct (op_raw2 D (off0 + 4) (n0 - 4) ltac:(lia)) as (EW & EC).
  replace (off0 + 4 + 1) with (off0 + 5) in EW by lia.
  exact (DTAIL regsK memK mdK _ _ _ (p + off0 + 1 + 2) HJK K11 K12 K22 K23 K24 KRK KMK GAK _ _ (p + off0 + 1 + 2 + 3)
    (n0 - 3 - 3) (p + off0 + 1 + 2 + 1) (n0 - 3 - 1) (TOP.FuzzIn (off0 + 4) (n0 - 4)) EKD Hd EW
    ltac:(rewrite EC; cbn [TOP.fi_off]; lia) ltac:(rewrite EC; cbn [TOP.fi_n]; lia) ltac:(cbn [TOP.fi_off]; lia)
    ltac:(cbn [TOP.fi_n]; lia)).
Qed.

End pc.

Section main. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* OP4A: from the arm of op 4 to SUBR (g_raw <> 0) or SUBT (g_raw = 0). *)
Lemma lc_op4a_ok : lc_op4a_stmt B MT XL RLO RHI.
Proof.
unfold lc_op4a_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & Ec & Ho & HL & Htw & Hcur0 & Hcur1 & Hs46).
subst c'.
pose proof HL as (HC & Hfr & Hsp & Hfsh & Hopok & He & Hmet & R19).
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_memset _ _ _ _ _ HP (l_fx cx)) as HMS.
pose proof (lp_recv_cells _ _ _ _ _ HP) as HRC.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof asan_consts as ((C1 & C2) & _).
pose proof Hopok as (Hagree & Hops & HFI & Hn0 & Hk).
destruct Hfr as (R18 & R26). destruct Hcur0 as (R25 & R23). destruct Hcur1 as (R24 & R27).
destruct Hs46 as (R20 & R22).
pose proof HIN as (HG8 & HPAYv).
unfold LF_FRAME in Hsp1. unfold LF_FBYTES in HFceil.
assert (SPL : forall o, In o (lf_spill_loop (lc_F cx)) ->
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + fst o) = Some (snd o))
  by (intros o Ho'; unfold lc_spills in Hsp; rewrite Forall_forall in Hsp; exact (Hsp o Ho')).
pose proof (SPL (112, TB_g_s) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app In];
  repeat (first [left; reflexivity | right]))) as H112.
pose proof (SPL (168, TB_M) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; repeat (first [left; reflexivity | right]))) as H168.
pose proof (SPL (184, transportb_hi 10) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; repeat (first [left; reflexivity | right]))) as H184.
pose proof (SPL (104, transportb_hi 8) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; repeat (first [left; reflexivity | right]))) as H104.
pose proof (SPL (144, lc_F cx + 32) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; repeat (first [left; reflexivity | right]))) as H144.
cbn [fst snd] in H112, H168, H184, H104, H144.
destruct op4_pages as (EP10 & EP8 & _ & _). rewrite EP10 in H184. rewrite EP8 in H104.
assert (Hnp : 0 < l_n cx).
{ destruct HFI as (Ho0 & Hn1 & Hon). destruct Hn as (_ & Hnl). lia. }
pose proof (HINg Hnp) as Hin.
assert (EPC0 : w64 (transportb_text + lo_arm 4) = Z_to_bv 64 (BASE + O_ARM))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC0.
apply (op4_main B LAWS HGX HMS HRC LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
  [(LF_CID, l_fpos cx)] ly' S' W' e (lc_F cx) (lc_sp1 cx) (l_fpos cx)
  (or_introl eq_refl) HFin HFaddr HF4096 HFal HFceil Hsp1c
  ltac:(destruct Hstk as (_ & _ & S3 & S4); lia) Hsp1al Hsp1 Hsp0al ltac:(unfold ESTACK, LLVMF_STK; lia)
  regs' mem' md' (lo_B op) (l_p cx) (l_n cx) (l_pl cx) (lo_c op) _ HJ Rsp Rgp Rtp R9 R18 R26 R20 R25 R23 R24 R27
  H112 H168 H184 H104 H144 Htw Hin (proj2 Hn) (proj2 (proj1 Hn)) HFI Hn0 HG8).
unfold op4_post.
intros regs2 mem2 md2 pc B4 HJ2 EOB Hbr Q21 KR TW2 HC2 ZSa ZSb KST KBK KFT GA.
apply SRr_ret. cbv beta.
assert (KRn : forall r, r = 18 \/ r = 19 \/ r = 26 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 ->
  YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r))
  by (intros r Hr; apply KR; first [unfold acallee_saved; lia | lia]).
pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
assert (HCORE : @lc_core rc B cx ly' S' W' regs2 mem2 md2 e).
{ apply (lc_core_kept_run B MT XL RLO RHI cx ly' S' W' regs' mem' md' e ly' S' W' regs2 mem2 md2 e HB HC HJ2 eq_refl
    (Permutation_refl _)).
  - intros r Hr. cbn [In] in Hr. apply KRn. lia.
  - intros a Ha. apply KST. lia.
  - intros i Hi. exact (KBK _ _ i Hin ltac:(lia)).
  - intros a Ha. apply KFT. unfold LF_FBYTES in Ha. lia.
  - intros a _ Ha. exact (GA a Ha). }
assert (HCOM : @lc_sub_common rc B MT cx op B4 ly' S' W' regs2 mem2 md2 e).
{ unfold lc_sub_common. cbv zeta.
  split; [exact (eq_sym Ho)|].
  split.
  { unfold lc_lcore. split; [exact HCORE|].
    split; [split; [exact (eq_trans (KRn 18 ltac:(lia)) R18) | exact (eq_trans (KRn 26 ltac:(lia)) R26)]|].
    split.
    { unfold lc_spills. rewrite Forall_forall. intros o Ho'.
      pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as V. rewrite Forall_forall in V.
      destruct (V o Ho') as (_ & Vm & V8 & V192).
      assert (H32 : 32 <= fst o).
      { assert (Hin' : In (fst o) (map fst (lf_spill_loop (lc_F cx)))) by (apply in_map; exact Ho').
        rewrite lf_spill_offsets in Hin'. cbn [In] in Hin'.
        repeat (destruct Hin' as [Hin' | Hin']; [lia|]). destruct Hin'. }
      rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem2) (lc_sp1 cx + fst o))
        by (intros j Hj; apply KST; lia).
      exact (SPL o Ho'). }
    split.
    { intros i Hi. unfold lc_SH. destruct (Z_lt_le_dec i 4) as [H4 | H4];
        [|destruct (Z_lt_le_dec i 8) as [H8 | H8]].
      - rewrite (ZSb i Hi ltac:(lia)), (lf_shm_tf i Hi ltac:(lia)). exact (Hfsh i Hi).
      - rewrite (ZSa i (conj H4 H8)), (lf_shm_tc i (conj H4 H8)). reflexivity.
      - rewrite (ZSb i Hi ltac:(lia)), (lf_shm_tf i Hi ltac:(lia)). exact (Hfsh i Hi). }
    split; [exact Hopok|]. split; [exact He|]. split; [exact Hmet|].
    exact (eq_trans (KRn 19 ltac:(lia)) R19). }
  split; [exact EOB|].
  split; [exact TW2 | exact HC2]. }
destruct Hbr as [(-> & Hg & Q11 & Q24 & Q23 & Q20 & Q22) | (-> & Hg & Q25 & Q22 & Q20 & H24)].
- left. unfold lc_st_subr. exists ly', S', regs2, mem2, md2, e, B4. cbv zeta.
  assert (EPC : Z_to_bv 64 (BASE + LO_SUBR) = w64 (transportb_text + LO_SUBR))
    by (unfold w64; f_equal; vm_compute; reflexivity).
  split; [unfold lc_cfg; rewrite EPC; reflexivity|].
  split; [exact HCOM|]. split; [exact Hg|].
  split; [exact Q21|]. split; [exact Q11|].
  split; [exact (conj Q24 Q23)|].
  exact (conj Q20 Q22).
- right. unfold lc_st_subt. exists ly', S', regs2, mem2, md2, e, B4. cbv zeta.
  assert (EPC : Z_to_bv 64 (BASE + LO_SUBT) = w64 (transportb_text + LO_SUBT))
    by (unfold w64; f_equal; vm_compute; reflexivity).
  split; [unfold lc_cfg; rewrite EPC; reflexivity|].
  split; [exact HCOM|]. split; [exact Hg|].
  split; [exact H24|].
  split; [exact (conj Q25 Q22) | exact Q20].
Qed.

End main.

Print Assumptions lc_op4a_ok.
