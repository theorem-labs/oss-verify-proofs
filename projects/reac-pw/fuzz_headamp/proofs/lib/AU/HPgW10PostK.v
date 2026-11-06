(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 692 of its 736 lines of code are new or changed and 246 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 548 of its 608 lines of code are new or changed and 676 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostTop.v at 01f4363fe7d, for image B of
   reac-pw/fuzz_headamp: w10t_ -> hw10p_, rs_ -> hsu_ (the cut states of lib/AU/HPgSeg.v), rm_ -> hm_, rl_ -> hd_;
   the entry states walk image B's own code (the arms split on what is left of the input as image B's tests do:
   0, 1, 2, 3, >= 4 bytes), with image B's UBSan tests decided by the atoms' range facts, the pod block reached from
   one atom (pp) whose 19744 bytes are one shadow entry, and pp->len's shadow address reloaded from R+0x150. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the builder's end P 0x82bec / P1 0x82bf0 of
   LLVMFuzzerTestOneInput (0x80c40), pod.h:440-444 with fuzz.h:39-42. Proves no function (kind: segment lemma).
   THE CODE (P1: a7 = the cursor, t3 = what is left of the input; s1 = R, s11 = K)
     0x82bec mv a7,s2                                  P only: the cursor moves from s2 to a7
     0x82bf0 .. 0x82bfc                                the check of pp->len (its shadow address from R+0x150)
     0x82c00 .. 0x82c20                                t2 = pp + 0x4000, a4 = pp, a5 = 0, s2 = pp (R+0x138, 0x30,
                                                       0x28, 0x148) and two UBSan tests on a5 (against 0x4001 and
                                                       against ~pp from R+0xf0)
     0x82c24 .. 0x82c6c                                the checks of the 4-byte store at pp and the four `sb` of
                                                       the top size word len - 8
     0x82c70 .. 0x82c74                                s8 = pp + 0x4d18 (R+0x120 + 4)
     0x82c78 beqz t3 -> 0x82ee0                        no input left: no corruption
     0x82c7c .. 0x82ca4 c = p[0]; bne c & 15, 15        -> 0x82ee0: no corruption
     0x82ca8 .. 0x82cc0 s5 = len; bltu s5, 9           -> 0x82ef4 -> C2 0x82efc: no corruption
     0x82cc4 bne t3,1 / 0x82ccc .. 0x82cd8              in.n = 1: a5 = a4 = a6 = 0, j 0x82dcc
     0x82cdc .. 0x82d00 p[1]; bne t3,2 / 0x82d04 ..    in.n = 2: a5 = a6 = 0, j 0x82dcc
     0x82da0 .. 0x82dc8 p[2], a5 = in.n - 3
     0x82dcc .. 0x82de4 a7 = len - 8 (a UBSan test: not 0)
     0x82de8 beqz a5 -> RT 0x82ec8                     in.n = 3: no byte written
     0x82dec .. 0x82e10 p[3]; beqz p[3] & 7 -> RT      the count is 0: no byte written
     0x82e14 .. 0x82e28 a3 = 0, a2 = p[3] & 7, a4 = (p[2] << 8 | p[1]) remu (len - 8) + 8, a0 = the cursor + 4,
                        a5 = in.n - 4, a6 = 1: R 0x82e2c with kk = 0
   The proof splits on |r| (0, 1, 2, 3, >= 4) and on the input's branches before it builds an entry state, so each
   arm is one engine run whose branch outcomes are the conds of its state. The first block's 19744 bytes and the
   input bytes read are shadow entries of the engine, so no check reaches its second test or its report.
   This file: the entry states, hw10p_leaf (which turns any arm's last state into the post cuts' common part), the
   model at the arms' ends and the Ltacs every arm uses; HPgW10PostN.v holds the arms |r| = 0, 1, 2, 3, HPgW10Post4.v the arm
   |r| >= 4, HPgW10Post.v the piece. HPgW10Req.hw10_tail finishes the 0x82ee0 arms. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW10Kit HPgW10Req.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* ---- the symbolic state at P1 ----
   atoms: 9 R, 17 the cursor (a7), 27 K, 28 what is left (t3); extra 32 pp, 33 len, 34 2^64 - 1 - pp (the
   complement R+0xf0 holds), 35 .. 38 the input bytes at the cursor *)
Definition hw10p_rtop : YP09.region := YP09.mkRegion (Some 32%nat) 0 4 0 4 [].
Definition hw10p_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x28 0x158 0 0
  [YP09.mkChunk 0x28 (CVal 8 (SLit 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xf0 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0x120 (CVal 8 (SOff 32 0x4d14)); YP09.mkChunk 0x138 (CVal 8 (SOff 32 0x4000));
   YP09.mkChunk 0x148 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x150 (CVal 8 (hw10_sh 32 0x4000))].
Definition hw10p_rlen : YP09.region := YP09.mkRegion (Some 32%nat) 0x4000 0x4008 0 0 [YP09.mkChunk 0x4000 (CVal 8 (SOff 33 0))].
Definition hw10p_rin (k : nat) : YP09.region := YP09.mkRegion (Some 17%nat) 0 (Z.of_nat k) 0 0
  (map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (35 + i) 0))) (seq 0 k)).
Definition hw10p_G0 (llo chi nlo nhi : Z) : list (nat * afact) :=
  [(27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 HW10_PPHI 4); (33%nat, mkAF llo 5440 0);
   (34%nat, mkAF (2 ^ 64 - 1 - HW10_PPHI) (2 ^ 64 - 4097) 0); (17%nat, mkAF 1 chi 0); (28%nat, mkAF nlo nhi 0)].
Definition hw10p_Gb (k : nat) : list (nat * afact) := map (fun i => ((35 + i)%nat, mkAF 0 255 0)) (seq 0 k).
(* |r| = 0 *)
Definition hw10p_ss0 (conds : list acond) : sstate :=
  mkSS HW10_P1 sr_atoms [hw10p_rtop; hw10p_rR; hw10p_rlen] None (mkFacts (hw10p_G0 8 (2 ^ 47) 0 0) conds []).
(* |r| >= 1: k input bytes known at the cursor *)
Definition hw10p_ssk (k : nat) (llo chi nlo nhi : Z) (conds : list acond) : sstate :=
  mkSS HW10_P1 sr_atoms [hw10p_rtop; hw10p_rR; hw10p_rlen; hw10p_rin k] None
  (mkFacts (hw10p_G0 llo chi nlo nhi ++ hw10p_Gb k) conds []).
(* the branches on the input: 0x82ca4 `bne` on c & 15 against 15, 0x82cc0 `bltu` on len against 9, the tests of
   what is left (0x82c78 `beqz`, 0x82cc8 `bne` 1, 0x82d00 `bne` 2, 0x82de8 `beqz` on in.n - 3), 0x82e10 `beqz` on the
   count byte & 7 *)
Definition hw10p_cNE15 : acond := mkAC BC_NE (SAlu ALU_AND (SOff 35 0) (SLit 15)) (SLit 15).
Definition hw10p_cEQ15 : acond := mkAC BC_EQ (SAlu ALU_AND (SOff 35 0) (SLit 15)) (SLit 15).
Definition hw10p_cLT9 : acond := mkAC BC_LTU (SOff 33 0) (SLit 9).
Definition hw10p_cN0 : acond := mkAC BC_EQ (SOff 28 0) (SLit 0).
Definition hw10p_cN1 : acond := mkAC BC_EQ (SOff 28 0) (SLit 1).
Definition hw10p_cN2 : acond := mkAC BC_EQ (SOff 28 0) (SLit 2).
Definition hw10p_cN3 : acond := mkAC BC_EQ (SOff 28 (-3)) (SLit 0).
Definition hw10p_cEQ7 : acond := mkAC BC_EQ (SAlu ALU_AND (SOff 38 0) (SLit 7)) (SLit 0).
Definition hw10p_cNE7 : acond := mkAC BC_NE (SAlu ALU_AND (SOff 38 0) (SLit 7)) (SLit 0).
(* the condition of what is left, for |r| = 1, 2, 3 *)
Definition hw10p_cN (k : nat) : acond := match k with 1%nat => hw10p_cN1 | 2%nat => hw10p_cN2 | _ => hw10p_cN3 end.
Definition hw10p_SH (k : nat) : list shent := [mkSHE 32 0 0x4d20; mkSHE 17 0 (Z.of_nat k)].

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma hw10p_in_byte : forall (H : word -> bool) mem src rest r i,
  garr8 rsegs (mrestrict H mem) src (hd_zbytes rest) -> hsu_suffix rest r -> (i < length r)%nat ->
  val_mem rsegs (mrestrict H mem) (src + Z.of_nat (length rest) - Z.of_nat (length r) + Z.of_nat i) 1
    (bv_unsigned (nth i r (Z_to_bv 8 0))).
Proof.
intros H mem src rest r i G (j & Hj & ->) Hi.
rewrite length_skipn in *.
assert (Hji : (j + i < length rest)%nat) by lia.
destruct (G (j + i)%nat) as [V _]; [unfold hd_zbytes; rewrite length_map; exact Hji|].
unfold hd_zbytes in V. rewrite hm_nth_map in V. rewrite nth_skipn.
replace (src + Z.of_nat (length rest) - Z.of_nat (length rest - j) + Z.of_nat i) with (src + Z.of_nat (j + i)) by lia.
replace (i + j)%nat with (j + i)%nat by lia. exact V.
Qed.

(* an 8-byte chunk from a cut's cell fact (HPgBase.hd_at: the value mod 2^64) *)
Lemma hw10p_ch8 : forall E m R off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem rsegs m (R + off) 8 (v mod 2 ^ 64) -> YP09.chunk_ok rsegs E m R (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E m R off e v He Hv V. rewrite Z.mod_small in V by lia.
apply (chunk_ok_val rsegs E m R off 8 e v He); [cbn; lia | cbn; lia | exact V].
Qed.

(* ---- the top size word read back out of the engine's region at atom 32 ---- *)
Lemma hw10p_le_byte : forall v k, 0 <= v < 2 ^ 32 ->
  Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)) = Z_to_bv 8 (YO0f.le_byte v 4 k).
Proof.
intros v k Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v) by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma hw10p_chunk_byte : forall E m b o e w, YP09.chunk_ok rsegs E m b (YP09.mkChunk o (CVal 1 e)) ->
  bv_unsigned (sv_denot E e) = w -> mbyte rsegs m (b + o) = Some (Z_to_bv 8 w).
Proof.
intros E m b o e w Hc Hw. destruct (Hc 0) as (x & Hx & Hm); [cbn; lia|].
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hx, Hm. unfold byte_of_word in Hx.
rewrite Z.mul_0_r, Z.shiftr_0_r, Hw in Hx. injection Hx as <-. rewrite Z.add_0_r in Hm. exact Hm.
Qed.

Lemma hw10p_top_val : forall E m cs L pp,
  region_ok rsegs E m (YP09.mkRegion (Some 32%nat) 0 4 0 4 cs) ->
  bv_unsigned (ew E 32) = pp -> ew E 33 = Z_to_bv 64 L -> 8 <= L <= 5440 ->
  In (YP09.mkChunk 0 (CVal 1 (SOff 33 (-8)))) cs ->
  In (YP09.mkChunk 1 (CVal 1 (SAlu ALU_SRL (SOff 33 (-8)) (SLit 8)))) cs ->
  In (YP09.mkChunk 2 (CVal 1 (SAlu ALU_SRL (SOff 33 (-8)) (SLit 16)))) cs ->
  In (YP09.mkChunk 3 (CVal 1 (SAlu ALU_SRL (SOff 33 (-8)) (SLit 24)))) cs ->
  val_mem rsegs m pp 4 (L - 8).
Proof.
intros E m cs L pp HR H32 H33 HL I0 I1 I2 I3.
destruct HR as (_ & _ & _ & Hcs). cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite H32 in Hcs.
assert (U0 : U E (SOff 33 (-8)) = L - 8) by (apply (U_atom_off E 33 L (-8) H33); lia).
assert (Us : forall s, 0 <= s < 64 -> U E (SAlu ALU_SRL (SOff 33 (-8)) (SLit s)) = Z.shiftr (L - 8) s).
{ intros s Hs. rewrite U_SAlu. cbn [zalu_raw]. rewrite U0, U_SLit. rewrite (zcanon_id s) by (unfold M64; lia).
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small s) by (change (2 ^ 6) with 64; lia).
  apply zcanon_id. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert ((L - 8) / 2 ^ s <= L - 8) by (apply Z.div_le_upper_bound; nia).
  assert (0 <= (L - 8) / 2 ^ s) by (apply Z.div_pos; lia). unfold M64. lia. }
pose proof (proj1 (Forall_forall _ _) Hcs) as Hc.
intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
- change (pp + Z.of_nat 0) with (pp + 0).
  rewrite (hw10p_chunk_byte E m pp 0 _ (L - 8) (Hc _ I0) U0).
  rewrite <- (hw10p_le_byte (L - 8) 0) by lia. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- change (pp + Z.of_nat 1) with (pp + 1).
  rewrite (hw10p_chunk_byte E m pp 1 _ _ (Hc _ I1) (Us 8 ltac:(lia))).
  rewrite <- (hw10p_le_byte (L - 8) 1) by lia. reflexivity.
- change (pp + Z.of_nat 2) with (pp + 2).
  rewrite (hw10p_chunk_byte E m pp 2 _ _ (Hc _ I2) (Us 16 ltac:(lia))).
  rewrite <- (hw10p_le_byte (L - 8) 2) by lia. reflexivity.
- change (pp + Z.of_nat 3) with (pp + 3).
  rewrite (hw10p_chunk_byte E m pp 3 _ _ (Hc _ I3) (Us 24 ltac:(lia))).
  rewrite <- (hw10p_le_byte (L - 8) 3) by lia. reflexivity.
Qed.

(* ---- the semantic end of every arm: what a run from P1 that wrote the top size word leaves ---- *)
Lemma hw10p_leaf : forall cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  hsu_Pbody rsegs B MT headamp_himg_B cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_P rsegs cx) ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall rr : Z, In rr [2; 3; 4; 8; 9; 19; 27] -> getr regs3 (Z_to_bv 5 rr) = getr regs2 (Z_to_bv 5 rr)) ->
  getr regs3 (Z_to_bv 5 7) = w64 (e_pp (x_e cx) + Layout.OFF_LEN) ->
  getr regs3 (Z_to_bv 5 18) = w64 (e_pp (x_e cx)) ->
  getr regs3 (Z_to_bv 5 24) = w64 (e_pp (x_e cx) + Layout.OFF_CORRUPT) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx)) 4 (hsu_plen sh ps - 8) ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs3 mem3 md3 /\
  hsu_at_cx rsegs cx W2 mem3 regs3 (hsu_L_post rsegs cx) /\
  hsu_fsh_at rsegs cx W2 mem3 (hsu_P0 headamp_himg_B) /\
  hsu_pp_at rsegs cx W2 mem3 (pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false).
Proof.
intros cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HP HB HL HJ3 Hio Hk R7 R18 R24 HK HV.
destruct HB as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & _).
destruct (hw10_ctx B MT cx _ ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR32 & HRS & HSTK & Hceil & H47 & HAR).
unfold T_SEG_STK, ASTACK in HSTK.
destruct (hw10_F_ctx B cx _ HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (hw10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
assert (HL3 : hsu_at_cx rsegs cx W2 mem3 regs3 (hsu_L_P rsegs cx)).
{ apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ HL).
  intros f Hf. unfold hsu_L_P in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv];
    first [ solve [apply Hk; repeat first [left; reflexivity | right]]
          | solve [intros i Hi; apply HK; lia] ] |]).
  destruct Hf. }
unfold hsu_at_cx, hsu_at, hsu_L_P in HL3. cbv zeta in HL3.
rewrite !Forall_cons_iff in HL3.
destruct HL3 as (P8 & P9 & P19 & P27 & Q08 & Q18 & Q20 & Q28 & Q30 & Q38 & Q48 & Qe0 & Qf0 & Q108 & Q120 & Q138 & Q148 & Q150 & _).
split; [|split; [|split]].
- apply (hw10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (fun a => e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) HC HJ3).
  + intros rr Hr. apply Hk. destruct Hr as [->|[->| ->]]; repeat first [left; reflexivity | right].
  + exact Hio.
  + exact HK.
  + intros a Ha. right. unfold PP_SIZE. lia.
- unfold hsu_at_cx, hsu_at, hsu_L_post. cbv zeta.
  repeat apply Forall_cons;
  [exact P8 | exact P9 | exact P19 | exact P27 | exact R7 | exact R18 | exact R24
  | exact Q08 | exact Q18 | exact Q20 | exact Q38 | exact Q48 | exact Qe0 | exact Q108 | exact Q120 | exact Q148
  | exact Q150 | apply Forall_nil].
- apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (e_F (x_e cx)) (hsu_P0 headamp_himg_B) Hfsh).
  intros i Hi. change (length (hsu_P0 headamp_himg_B)) with 116%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)).
  assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia|].
  pose proof (hw10_shadow_not_pp (e_pp (x_e cx)) (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs. unfold PP_SIZE in Hs. lia.
- rewrite <- (hw10_img_top sh ps Hwf). unfold le32.
  assert (HLI : Z.of_nat (length (pc_image (PbCut sh ps None))) = PP_SIZE).
  { unfold pc_image. apply length_pp_image; [unfold POD_BUF_MAX in *; lia | |].
    - rewrite (pc_ents_final sh ps None). exact HW3.
    - rewrite (pc_ents_final sh ps None). exact HW4. }
  apply (hm_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem3 (e_pp (x_e cx)) _ 0 4 _ Hpp).
  + replace (e_pp (x_e cx) + Z.of_nat 0) with (e_pp (x_e cx)) by lia. exact HV.
  + unfold PP_SIZE in HLI. lia.
  + intros y Hy Hn. rewrite HLI in Hy. unfold PP_SIZE in Hy. apply HK; [lia|]. cbn in Hn. lia.
Qed.

(* the len cell of the first block *)
Lemma hw10p_len_cell : forall cx sh ps W2 mem2, hsu_wf sh ps ->
  hsu_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps None)) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (hsu_plen sh ps).
Proof.
intros cx sh ps W2 mem2 Hwf Hpp. destruct (hw10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
unfold hsu_pp_at, pc_image in Hpp. rewrite (pc_ents_final sh ps None) in Hpp.
exact (hm_pp_len rsegs (pc_buf (PbCut sh ps None)) _ _ _ _ _ ltac:(unfold POD_BUF_MAX; lia) HW3 HW4
  (w_H W2) mem2 (e_pp (x_e cx)) Hpp).
Qed.

Definition hw10p_clob : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%bv.

(* ---- the input bytes at the cursor, at the cut's memory ---- *)
Lemma hw10p_in_at : forall cx rest r (W2 : world rsegs) mem2 i,
  hsu_in rsegs headamp_himg_B cx rest ->
  garr8 rsegs (mrestrict (w_H W2) mem2) (e_src (x_e cx)) (hd_zbytes rest) ->
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e cx)) (e_left (x_e cx)) ->
  hsu_suffix rest r -> (i < length r)%nat ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (hsu_cur rsegs cx rest r + Z.of_nat i) 1
    (bv_unsigned (nth i r (Z_to_bv 8 0))) /\
  ~ (e_R (x_e cx) <= hsu_cur rsegs cx rest r + Z.of_nat i < e_R (x_e cx) + 0x198) /\
  ~ (e_pp (x_e cx) <= hsu_cur rsegs cx rest r + Z.of_nat i < e_pp (x_e cx) + PP_SIZE) /\
  e_src (x_e cx) <= hsu_cur rsegs cx rest r + Z.of_nat i < e_src (x_e cx) + e_left (x_e cx).
Proof.
intros cx rest r W2 mem2 i HI G Hra Hsuf Hi.
pose proof Hsuf as (j & Hj & Hr).
assert (Hlr : length r = (length rest - j)%nat) by (rewrite Hr, length_skipn; reflexivity).
pose proof HI as (Hleft & _ & _ & _ & _ & _ & _ & Hdisj).
unfold hsu_cur.
assert (Hx : e_src (x_e cx) <= e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r) + Z.of_nat i
  < e_src (x_e cx) + e_left (x_e cx)) by lia.
destruct (Hdisj _ Hx) as (D1 & D2 & D3).
split; [exact (hw10p_in_byte _ _ _ _ _ _ G Hsuf Hi)|].
split; [|split; [exact D3 | exact Hx]].
intros X. apply D2. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.

(* ---- the region of R's cells ---- *)
Lemma hw10p_rR_ok : forall E (H : word -> bool) mem R pp,
  bv_unsigned (ew E 9) = R -> ew E 27 = Z_to_bv 64 SHADOW_OFF ->
  ew E 32 = Z_to_bv 64 pp -> ew E 34 = Z_to_bv 64 (2 ^ 64 - 1 - pp) ->
  0 <= R -> R + 0x158 <= 2 ^ 64 -> 0 <= pp -> pp + 0x4d20 <= 2 ^ 47 ->
  val_mem rsegs (mrestrict H mem) (R + 0x28) 8 (0 mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0x30) 8 (pp mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0x120) 8 ((pp + 0x4d14) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0x138) 8 ((pp + 0x4000) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0x148) 8 (pp mod 2 ^ 64) ->
  val_mem rsegs (mrestrict H mem) (R + 0x150) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
  region_ok rsegs E (mrestrict H mem) hw10p_rR.
Proof.
intros E H mem R pp E9 E27 E32 E34 HR0 HR1 Hp0 Hp1 Q28 Q30 Qf0 Q120 Q138 Q148 Q150.
apply (hm_ro_region rsegs E H mem 9 R); [exact E9 | lia | lia |].
repeat apply Forall_cons; [..|apply Forall_nil].
- apply (hw10p_ch8 _ _ _ _ _ 0); [reflexivity | lia | exact Q28].
- apply (hw10p_ch8 _ _ _ _ _ pp); [exact (hw10_den_atom _ 32 _ E32) | lia | exact Q30].
- apply (hw10p_ch8 _ _ _ _ _ (2 ^ 64 - 1 - pp)); [exact (hw10_den_atom _ 34 _ E34) | lia |].
  assert (Eq : (2 ^ 64 - 1 - pp) mod 2 ^ 64 = (- pp - 1) mod 2 ^ 64).
  { replace (2 ^ 64 - 1 - pp) with ((- pp - 1) + 1 * 2 ^ 64) by lia. apply Z.mod_add. lia. }
  rewrite Eq. exact Qf0.
- apply (hw10p_ch8 _ _ _ _ _ (pp + 0x4d14)); [exact (hw10_den_off _ 32 _ _ E32) | lia | exact Q120].
- apply (hw10p_ch8 _ _ _ _ _ (pp + 0x4000)); [exact (hw10_den_off _ 32 _ _ E32) | lia | exact Q138].
- apply (hw10p_ch8 _ _ _ _ _ pp); [exact (hw10_den_atom _ 32 _ E32) | lia | exact Q148].
- apply (hw10p_ch8 _ _ _ _ _ (shadow_addr (pp + 0x4000)));
  [exact (hw10_den_sh _ 32 pp 0x4000 E32 ltac:(lia) ltac:(lia) E27) | | exact Q150].
  unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia) ltac:(lia)).
  assert ((pp + 0x4000) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma hw10p_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2. induction l1 as [|[n f] l IH]; cbn; [auto | intros [H1 H2] H; split; auto]. Qed.

Lemma hw10p_G0_ok : forall E pp L cur n llo chi nlo nhi,
  ew E 27 = Z_to_bv 64 SHADOW_OFF -> ew E 32 = Z_to_bv 64 pp -> ew E 33 = Z_to_bv 64 L ->
  ew E 34 = Z_to_bv 64 (2 ^ 64 - 1 - pp) -> ew E 17 = Z_to_bv 64 cur -> ew E 28 = Z_to_bv 64 n ->
  4096 <= pp <= HW10_PPHI -> pp mod 16 = 0 -> llo <= L <= 5440 -> 0 <= llo -> 1 <= cur <= chi -> chi < 2 ^ 64 ->
  nlo <= n <= nhi -> 0 <= nlo -> n < 2 ^ 64 ->
  atoms_ok E (hw10p_G0 llo chi nlo nhi).
Proof.
intros E pp L cur n llo chi nlo nhi E27 E32 E33 E34 E17 E28 Hp Hal HL Hllo Hc Hchi Hn Hnlo Hn64.
unfold hw10p_G0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E27, E32, E33, E34, E17, E28, !unsigned_lit_small by (unfold SHADOW_OFF, HW10_PPHI in *; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
unfold SHADOW_OFF, HW10_PPHI in *. repeat split; try assumption; try lia.
Qed.

Lemma hw10p_Gb_ok : forall E (r : list byte) k,
  (forall i, (i < k)%nat -> ew E (35 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  atoms_ok E (hw10p_Gb k).
Proof.
intros E r k H. unfold hw10p_Gb.
assert (G : forall s, (forall i, (s <= i < s + k)%nat ->
    ew E (35 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  atoms_ok E (map (fun i => ((35 + i)%nat, mkAF 0 255 0)) (seq s k))).
{ clear H. induction k as [|k IH]; intros s Hs; cbn [seq map atoms_ok]; [exact I|]. split.
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (Hs s ltac:(lia)).
    pose proof (hm_byte_range (nth s r (Z_to_bv 8 0))) as Hb. rewrite unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
  - apply IH. intros i Hi. apply Hs. lia. }
apply G. intros i Hi. apply H. lia.
Qed.

Lemma hw10p_rin_ok : forall E (H : word -> bool) mem cur (r : list byte) k,
  bv_unsigned (ew E 17) = cur -> 0 <= cur -> cur + Z.of_nat k <= 2 ^ 64 ->
  (forall i, (i < k)%nat -> ew E (35 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  (forall i, (i < k)%nat ->
     val_mem rsegs (mrestrict H mem) (cur + Z.of_nat i) 1 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  region_ok rsegs E (mrestrict H mem) (hw10p_rin k).
Proof.
intros E H mem cur r k H17 H0 H1 HE HV.
apply (hm_ro_region rsegs E H mem 17 cur); [exact H17 | lia | exact H1 |].
apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (i & <- & Hi). apply in_seq in Hi.
pose proof (hm_byte_range (nth i r (Z_to_bv 8 0))) as Hb.
apply (chunk_ok_val rsegs E _ cur (Z.of_nat i) 1 (SOff (35 + i) 0) (bv_unsigned (nth i r (Z_to_bv 8 0)))).
- apply hw10_den_atom. apply HE. lia.
- cbn. lia.
- cbn. lia.
- apply HV. lia.
Qed.

(* ---- one arm's entry state (|r| >= 1; the arm's branch outcomes are the conds of its state) ---- *)
Lemma hw10p_HS_lem : forall (cx : hsu_scx rsegs) (r : list byte) (W2 : world rsegs) regs2 mem2 E ex L cur k
  llo chi nlo nhi conds,
  E = Ereg regs2 ex ->
  ew E 9 = Z_to_bv 64 (e_R (x_e cx)) -> ew E 27 = Z_to_bv 64 SHADOW_OFF ->
  ew E 17 = Z_to_bv 64 cur -> ew E 28 = Z_to_bv 64 (Z.of_nat (length r)) ->
  ew E 32 = Z_to_bv 64 (e_pp (x_e cx)) -> ew E 33 = Z_to_bv 64 L ->
  ew E 34 = Z_to_bv 64 (2 ^ 64 - 1 - e_pp (x_e cx)) ->
  (forall i, (i < 4)%nat -> ew E (35 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) ->
  2 ^ 44 <= e_R (x_e cx) -> e_R (x_e cx) + 0x220 <= 2 ^ 47 ->
  4096 <= e_pp (x_e cx) -> e_pp (x_e cx) + 19744 <= e_R (x_e cx) -> e_pp (x_e cx) mod 16 = 0 ->
  e_pp (x_e cx) <= HW10_PPHI -> 0 <= llo -> llo <= L <= 5440 ->
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + 19744 -> apresent (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x28) 8 (0 mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x30) 8 (e_pp (x_e cx) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0xf0) 8 ((- e_pp (x_e cx) - 1) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x120) 8 ((e_pp (x_e cx) + 0x4d14) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x138) 8 ((e_pp (x_e cx) + 0x4000) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x148) 8 (e_pp (x_e cx) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x150) 8 (shadow_addr (e_pp (x_e cx) + 0x4000) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 L ->
  (forall i, (i < k)%nat ->
     val_mem rsegs (mrestrict (w_H W2) mem2) (cur + Z.of_nat i) 1 (bv_unsigned (nth i r (Z_to_bv 8 0))) /\
     ~ (e_R (x_e cx) <= cur + Z.of_nat i < e_R (x_e cx) + 0x198) /\
     ~ (e_pp (x_e cx) <= cur + Z.of_nat i < e_pp (x_e cx) + PP_SIZE)) ->
  (0 < k <= 4)%nat -> 1 <= cur <= chi -> chi + Z.of_nat k <= 2 ^ 47 ->
  nlo <= Z.of_nat (length r) <= nhi -> 0 <= nlo -> Z.of_nat (length r) < 2 ^ 64 ->
  conds_ok E conds ->
  st_ok rsegs E (hw10p_ssk k llo chi nlo nhi conds) (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_P1) mem2 (seg_rom rsegs))).
Proof.
intros cx r W2 regs2 mem2 E ex L cur k llo chi nlo nhi conds HE E9 E27 E17 E28 E32 E33 E34 EB
  HR0 HR1 Hp0 HpR Hal Hpp Hllo HL Hpres Q28 Q30 Qf0 Q120 Q138 Q148 Q150 HLv HIN Hk Hc Hchi Hnl Hnlo Hnl64 Hco.
assert (U9 : bv_unsigned (ew E 9) = e_R (x_e cx)) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = e_pp (x_e cx)) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U17 : bv_unsigned (ew E 17) = cur) by (rewrite E17; apply unsigned_lit_small; lia).
destruct (HIN 0%nat ltac:(lia)) as (_ & NRa & NPa).
destruct (HIN (k - 1)%nat ltac:(lia)) as (_ & NRb & NPb).
assert (Hwf : regions_wf [hw10p_rtop; hw10p_rR; hw10p_rlen; hw10p_rin k] = true).
{ destruct k as [|[|[|[|[|k]]]]]; try lia; vm_compute; reflexivity. }
rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- apply Forall_cons.
  { apply (hm_rw_region rsegs _ (w_H W2) mem2 32 (e_pp (x_e cx)));
    [exact U32 | lia | lia | intros o Ho; apply Hpres; lia | constructor]. }
  apply Forall_cons.
  { apply (hw10p_rR_ok _ _ _ _ _ U9 E27 E32 E34); try lia; assumption. }
  apply Forall_cons.
  { apply (hm_ro_region rsegs _ (w_H W2) mem2 32 (e_pp (x_e cx))); [exact U32 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (e_pp (x_e cx)) 0x4000 8 (SOff 33 0) L);
      [exact (hw10_den_atom _ 33 L E33) | cbn; lia | cbn; lia | exact HLv]. }
  apply Forall_cons; [| apply Forall_nil].
  apply (hw10p_rin_ok _ _ _ cur r); [exact U17 | lia | lia | intros i Hi; apply EB; lia | intros i Hi; exact (proj1 (HIN i Hi))].
- apply pairwise_disjoint_of_extents.
  cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
  cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd hw10p_rtop hw10p_rR hw10p_rlen hw10p_rin].
  rewrite U9, U32, U17.
  unfold PP_SIZE in *. repeat split; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split; [exact Hco | cbn; exact I]].
  apply hw10p_atoms_app; [|exact (hw10p_Gb_ok _ r k (fun i Hi => EB i ltac:(lia)))].
  apply (hw10p_G0_ok _ (e_pp (x_e cx)) L cur (Z.of_nat (length r))); try assumption; try lia.
Qed.

(* ---- one arm's end: the leaf's four facts from the run's last state ---- *)
Lemma hw10p_fin_lem : forall cx sh np ps rest r ly2 S2 (W2 : world rsegs) regs2 mem2 md2 E ex E' ss ms md3 rs0 cs,
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  hsu_Pbody rsegs B MT headamp_himg_B cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_P rsegs cx) ->
  E = Ereg regs2 ex ->
  ew E 32 = Z_to_bv 64 (e_pp (x_e cx)) -> ew E 33 = Z_to_bv 64 (hsu_plen sh ps) ->
  st_ok rsegs E' ss (restrict (w_H W2) ms) -> env_agree 34 E E' ->
  forallb (fun r0 : bv 5 => existsb (fun c => bv_eqb c r0) hw10p_clob
    || sv_eqb (sr_get (ss_regs ss) r0) (SOff (Z.to_nat (bv_unsigned r0)) 0)) HPgSteps.nz_regs = true ->
  sr_get (ss_regs ss) (Z_to_bv 5 7) = SOff 32 0x4000 -> sr_get (ss_regs ss) (Z_to_bv 5 18) = SOff 32 0 ->
  sr_get (ss_regs ss) (Z_to_bv 5 24) = SOff 32 0x4d18 ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 32%nat) 0 4 0 4 cs) ->
  In (YP09.mkChunk 0 (CVal 1 (SOff 33 (-8)))) cs ->
  In (YP09.mkChunk 1 (CVal 1 (SAlu ALU_SRL (SOff 33 (-8)) (SLit 8)))) cs ->
  In (YP09.mkChunk 2 (CVal 1 (SAlu ALU_SRL (SOff 33 (-8)) (SLit 16)))) cs ->
  In (YP09.mkChunk 3 (CVal 1 (SAlu ALU_SRL (SOff 33 (-8)) (SLit 24)))) cs ->
  frame_of E rs0 (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms)) ->
  (forall a, in_wrange E rs0 a -> e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 (ms_mem ms) md3 (x_k cx) ->
  same_io md2 md3 ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 /\
  hsu_at_cx rsegs cx W2 (ms_mem ms) (ms_regs ms) (hsu_L_post rsegs cx) /\
  hsu_fsh_at rsegs cx W2 (ms_mem ms) (hsu_P0 headamp_himg_B) /\
  hsu_pp_at rsegs cx W2 (ms_mem ms) (pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false).
Proof.
intros cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E ex E' ss ms md3 rs0 cs HP HB HL HE E32 E33
  HS HAE Hck H7 H18 H24 Hnth I0 I1 I2 I3 HFr Hwr HJ Hio.
pose proof HB as (HC & _ & _ & _ & _ & Hwf & _).
destruct (hw10_ctx B MT cx _ ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR32 & HRS & HSTK & Hceil & H47 & HAR).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (hw10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5). unfold hsu_plen in *.
assert (HAE32 : env_agree 32 (Ereg regs2 ex) E') by (rewrite <- HE; eapply env_agree_le; [|exact HAE]; lia).
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros X. exact (Hn (Hwr a X)). }
pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2) hw10p_clob HS HAE32 Hck) as RK.
assert (Hk : forall rr : Z, In rr [2; 3; 4; 8; 9; 19; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 rr) = getr regs2 (Z_to_bv 5 rr)).
{ intros rr Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity] |]).
  destruct Hr. }
assert (R7 : getr (ms_regs ms) (Z_to_bv 5 7) = w64 (e_pp (x_e cx) + Layout.OFF_LEN)).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 7) 34 (SOff 32 0x4000) _ HS HAE H7); [reflexivity |].
  exact (hw10_den_off _ 32 _ _ E32). }
assert (R18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (e_pp (x_e cx))).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 18) 34 (SOff 32 0) _ HS HAE H18); [reflexivity |].
  exact (hw10_den_atom _ 32 _ E32). }
assert (R24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 (e_pp (x_e cx) + Layout.OFF_CORRUPT)).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 34 (SOff 32 0x4d18) _ HS HAE H24); [reflexivity |].
  exact (hw10_den_off _ 32 _ _ E32). }
assert (HV : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (e_pp (x_e cx)) 4
  (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8)).
{ apply (hw10p_top_val _ _ _ _ (e_pp (x_e cx)) (HPgSteps.st_ok_region_at _ _ _ 0 _ HS Hnth)); [| | lia | exact I0 | exact I1 | exact I2 | exact I3].
  - transitivity (bv_unsigned (ew E 32)); [f_equal; exact (proj1 HAE 32%nat ltac:(lia)) | rewrite E32; apply unsigned_lit_small; lia].
  - transitivity (ew E 33); [exact (proj1 HAE 33%nat ltac:(lia)) | exact E33]. }
exact (hw10p_leaf cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) md3 HP HB HL HJ Hio
  Hk R7 R18 R24 HK HV).
Qed.


Lemma hw10p_U_and15 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 15)) = v mod 16.
Proof.
intros E n v H Hv. rewrite U_and_lit by lia. rewrite (U_atom E n v H) by lia.
change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma hw10p_U_and7 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 7)) = v mod 8.
Proof.
intros E n v H Hv. rewrite U_and_lit by lia. rewrite (U_atom E n v H) by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

(* a4 at R: (p[2] << 8 | p[1]) remu (len - 8) + 8 (0x82e18 .. 0x82e24) *)
Lemma hw10p_U_off : forall E xa xb L, ew E 36 = Z_to_bv 64 xa -> ew E 37 = Z_to_bv 64 xb ->
  ew E 33 = Z_to_bv 64 L -> 0 <= xa < 256 -> 0 <= xb < 256 -> 9 <= L <= 5440 ->
  U E (SAlu ALU_ADD (SMd M_REMU (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 36 0)) (SOff 33 (-8)))
    (SLit 8)) = 8 + (xa + 256 * xb) mod (L - 8).
Proof.
intros E xa xb L H36 H37 H33 Ba Bb HL.
assert (U36 : U E (SOff 36 0) = xa) by (apply U_atom; [exact H36 | lia]).
assert (U37 : U E (SOff 37 0) = xb) by (apply U_atom; [exact H37 | lia]).
assert (U33 : U E (SOff 33 (-8)) = L - 8) by (apply (U_atom_off E 33 L (-8) H33); lia).
assert (USL : U E (SAlu ALU_SLL (SOff 37 0) (SLit 8)) = Z.shiftl xb 8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U37, U_SLit. change (Z.land (zcanon 8) 63) with 8.
  apply zcanon_id. rewrite Z.shiftl_mul_pow2 by lia. unfold M64. lia. }
assert (UOR : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 36 0)) = xa + 256 * xb).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite USL, U36. rewrite Z.lor_comm, hm_lor_shift8 by lia.
  apply zcanon_id. unfold M64. lia. }
assert (UR : U E (SMd M_REMU (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 36 0)) (SOff 33 (-8)))
  = (xa + 256 * xb) mod (L - 8)).
{ rewrite U_SMd, UOR, U33. cbn [zmd_raw]. rewrite (proj2 (Z.eqb_neq (L - 8) 0)) by lia.
  pose proof (Z.mod_pos_bound (xa + 256 * xb) (L - 8) ltac:(lia)). apply zcanon_id. unfold M64. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite UR, U_SLit. change (zcanon 8) with 8.
pose proof (Z.mod_pos_bound (xa + 256 * xb) (L - 8) ltac:(lia)). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the model at the arms' ends ---- *)
Lemma hw10p_model_RT : forall L (c0 : byte) r1, bv_unsigned c0 mod 16 = 15 -> 9 <= L ->
  fst (fuzz_u8 (skipn 2 r1)) mod 8 = 0 ->
  fst (corr_step L (c0 :: r1)) = Some (8 + fst (fuzz_u16 r1) mod (L - 8), []) /\
  8 <= 8 + fst (fuzz_u16 r1) mod (L - 8) < L.
Proof.
intros L c0 r1 Hc HL H0. pose proof (fuzz_u16_range r1) as Hu.
pose proof (Z.mod_pos_bound (fst (fuzz_u16 r1)) (L - 8) ltac:(lia)) as Hm.
split; [|lia]. rewrite (hw10_corr_some L c0 r1 Hc ltac:(lia)). rewrite H0.
rewrite Z.min_l by lia. reflexivity.
Qed.

Lemma hw10p_model_R : forall L (c0 xa xb xc : byte) r4 off cnt bs,
  bv_unsigned c0 mod 16 = 15 -> 9 <= L -> bv_unsigned xc mod 8 <> 0 ->
  off = 8 + (bv_unsigned xa + 256 * bv_unsigned xb) mod (L - 8) -> cnt = bv_unsigned xc mod 8 ->
  bs = fst (fuzz_u8s (Z.to_nat (Z.min cnt (L - off))) r4) ->
  fst (corr_step L (c0 :: xa :: xb :: xc :: r4)) = Some (off, bs) /\ 8 <= off < L /\ 0 < cnt <= 7 /\
  Z.of_nat (length bs) = Z.min cnt (L - off) /\ bs = fst (fuzz_u8s (length bs) r4).
Proof.
intros L c0 xa xb xc r4 off cnt bs Hc HL Hx Ho Hn Hb.
pose proof (hm_byte_range xa). pose proof (hm_byte_range xb). pose proof (hm_byte_range xc).
pose proof (Z.mod_pos_bound (bv_unsigned xa + 256 * bv_unsigned xb) (L - 8) ltac:(lia)) as Hm.
pose proof (Z.mod_pos_bound (bv_unsigned xc) 8 ltac:(lia)) as Hm8.
split; [|split; [lia|split; [lia|split]]].
- rewrite (hw10_corr_some L c0 (xa :: xb :: xc :: r4) Hc ltac:(lia)). subst off cnt bs. reflexivity.
- rewrite Hb, hw10_length_fuzz_u8s. rewrite Z2Nat.id; [reflexivity | lia].
- rewrite Hb at 1. rewrite Hb, hw10_length_fuzz_u8s. reflexivity.
Qed.

(* ---- the targets' cuts from the leaf's four facts ---- *)
Lemma hw10p_mkC2 : forall cx rest ly2 S2 W2 regs3 mem3 md3,
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs3 mem3 md3 ->
  hsu_at_cx rsegs cx W2 mem3 regs3 (hsu_L_post rsegs cx) -> hsu_fsh_at rsegs cx W2 mem3 (hsu_P0 headamp_himg_B) ->
  hsu_pp_at rsegs cx W2 mem3 (pp_bytes (fst (pod_build rest))) -> e_len (x_e cx) = hd_len rest ->
  getr regs3 (Z_to_bv 5 10) = w64 (e_len (x_e cx)) -> getr regs3 (Z_to_bv 5 21) = w64 (e_len (x_e cx)) ->
  hsu_cut_C2 rsegs B MT headamp_himg_B cx rest ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest ly2 S2 W2 regs3 mem3 md3 L1 L2 L3 L4 Hlen R10 R21.
pose proof (hw10_len_bounds rest) as Hb.
split; [exact L1|]. split; [apply (hw10_L2_of_post cx (w_H W2) mem3 regs3 L2 R10 R21); lia|].
split; [exact L3|]. split; [exact L4 | exact Hlen].
Qed.

Lemma hw10p_mkRT : forall cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off,
  hsu_Pbody rsegs B MT headamp_himg_B cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs3 mem3 md3 ->
  hsu_at_cx rsegs cx W2 mem3 regs3 (hsu_L_post rsegs cx) -> hsu_fsh_at rsegs cx W2 mem3 (hsu_P0 headamp_himg_B) ->
  hsu_pp_at rsegs cx W2 mem3 (pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false) ->
  fst (pod_build rest) = PodRec sh ps (Some (off, [])) -> 8 <= off -> off <= hsu_plen sh ps ->
  hsu_cut_RT rsegs B MT headamp_himg_B cx sh ps off [] rest r ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off HB L1 L2 L3 L4 Ht Ho1 Ho2.
destruct HB as (_ & _ & _ & Hin & Hsuf & Hwf & Hlen & _).
split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
split; [unfold hsu_img_corr; cbn [length Z.of_nat Z.to_nat firstn]; rewrite hw10_overwrite_nil; exact L4|].
split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Ht|].
split; [exact Ho1|]. cbn [length Z.of_nat]. split; lia.
Qed.

Lemma hw10p_mkR : forall cx sh np ps rest r r' ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off bs cnt,
  hsu_Pbody rsegs B MT headamp_himg_B cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs3 mem3 md3 ->
  hsu_at_cx rsegs cx W2 mem3 regs3 (hsu_L_post rsegs cx) -> hsu_fsh_at rsegs cx W2 mem3 (hsu_P0 headamp_himg_B) ->
  hsu_pp_at rsegs cx W2 mem3 (pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false) ->
  getr regs3 (Z_to_bv 5 13) = w64 0 -> getr regs3 (Z_to_bv 5 12) = w64 cnt -> getr regs3 (Z_to_bv 5 14) = w64 off ->
  getr regs3 (Z_to_bv 5 16) = w64 1 ->
  getr regs3 (Z_to_bv 5 10) = w64 (hsu_cur rsegs cx rest r') ->
  getr regs3 (Z_to_bv 5 15) = w64 (Z.of_nat (length r')) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e cx) + 0xf0) 8 ((- e_pp (x_e cx) - 1) mod 2 ^ 64) ->
  hsu_suffix rest r' -> fst (pod_build rest) = PodRec sh ps (Some (off, bs)) -> hsu_corr_wf sh ps off bs cnt ->
  bs = fst (fuzz_u8s (length bs) r') ->
  hsu_cut_R rsegs B MT headamp_himg_B cx sh ps rest r' off bs cnt 0 ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx sh np ps rest r r' ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 off bs cnt HB L1 L2 L3 L4
  R13 R12 R14 R16 R10 R15 Qf0 Hsuf' Ht Hcw Hbs.
destruct HB as (_ & _ & _ & Hin & _ & Hwf & Hlen & _).
pose proof Hcw as (_ & _ & _ & Hcnt & _).
split; [exact L1|]. split.
{ unfold hsu_at_cx, hsu_at in *. apply Forall_app. split; [exact L2|].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd hd_at hd_xv].
  - exact R13. - rewrite Z.sub_0_r. exact R12. - exact R14. - exact R16. - exact R10. - exact R15. - exact Qf0. }
split; [exact L3|].
split; [unfold hsu_img_corr; cbn [Z.to_nat firstn]; rewrite hw10_overwrite_nil; exact L4|].
split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Ht|].
split; [exact Hcw|]. split; [lia|]. split; [lia|].
cbn [Z.to_nat skipn]. rewrite Nat.sub_0_r. exact Hbs.
Qed.

(* the condition on what is left, |r| = 1, 2, 3 *)
Lemma hw10p_cN_ok : forall E n k, ew E 28 = Z_to_bv 64 n -> n = Z.of_nat k -> (1 <= k <= 3)%nat ->
  acond_ok E (hw10p_cN k).
Proof.
intros E n k H28 Hn Hk. unfold acond_ok.
destruct k as [|[|[|[|k]]]]; try lia; cbn [hw10p_cN hw10p_cN1 hw10p_cN2 hw10p_cN3 ac_c ac_a ac_b];
rewrite branch_eq_U, U_lit by lia; apply Z.eqb_eq.
- rewrite (U_atom E 28 n H28) by lia. lia.
- rewrite (U_atom E 28 n H28) by lia. lia.
- rewrite (U_atom_off E 28 n (-3) H28) by lia. lia.
Qed.


End t.

(* ---- the common start of every arm: the cut's facts, by name ---- *)
Ltac hw10p_pre B MT HP HB HL :=
  pose proof HB as HB0;
  destruct HB as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Hsh & Hnp & Hnps & Hps);
  pose proof hw10_wx as Hwx; pose proof hw10_segs_low as Hsegs;
  pose proof (AR_laws_ok rsegs B) as LAWS;
  destruct (hw10_ctx B MT _ _ _ _ _ _ _ _ HP HC)
    as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR32 & HRS & HSTK & Hceil & H47 & HAR);
  unfold T_SEG_STK, ASTACK in HSTK;
  destruct (hw10_F_ctx B _ _ HP) as (HF1 & HF2 & HF3);
  destruct (hw10_pre_geom B _ _ HP) as (_ & HRk & HR47 & _ & _);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  destruct (hw10_wf_facts _ _ Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5);
  pose proof HL as HL0;
  unfold hsu_at_cx, hsu_at, hsu_L_P in HL; cbv zeta in HL; cbn [app] in HL;
  rewrite !Forall_cons_iff in HL;
  destruct HL as (P8 & P9 & P19 & P27 & Q08 & Q18 & Q20 & Q28 & Q30 & Q38 & Q48 & Qe0 & Qf0 & Q108 & Q120 & Q138
    & Q148 & Q150 & P17 & P28 & _);
  cbn [fst snd hd_at hd_xv] in P8, P9, P19, P27, Q08, Q18, Q20, Q28, Q30, Q38, Q48, Qe0, Qf0, Q108, Q120, Q138,
    Q148, Q150, P17, P28;
  unfold Layout.OFF_LEN, Layout.OFF_N_ENT in Q120, Q138, Q150;
  pose proof HC as (HJ & _).

(* the conds of an arm, from its branch facts (EB, E33, E28: the entry environment's atoms) *)
Ltac hw10p_cond1 EB E33 E28 :=
  unfold acond_ok, hw10p_cNE15, hw10p_cEQ15, hw10p_cLT9, hw10p_cN0, hw10p_cN1, hw10p_cN2, hw10p_cN3,
    hw10p_cN, hw10p_cEQ7, hw10p_cNE7;
  cbn [ac_c ac_a ac_b];
  first [ rewrite branch_ne_U | rewrite branch_eq_U | rewrite branch_ltu_U | rewrite branch_geu_U ];
  rewrite ?(hw10p_U_and15 _ 35 _ (EB 0%nat ltac:(lia)) (hm_byte_range _)),
          ?(hw10p_U_and7 _ 38 _ (EB 3%nat ltac:(lia)) (hm_byte_range _)),
          ?(hw10_U_atom _ 33 _ E33 ltac:(lia)), ?(hw10_U_atom _ 28 _ E28 ltac:(lia)), ?U_lit by lia;
  try cbn [nth];
  first [ apply negb_true_iff, Z.eqb_neq | apply Z.eqb_eq | apply Z.ltb_lt | apply negb_true_iff, Z.ltb_ge ];
  first [ assumption | lia ].
Ltac hw10p_conds EB E33 E28 := cbn [conds_ok]; repeat first [ exact I | split; [hw10p_cond1 EB E33 E28 |] ].

(* every write window of an entry state lies in [pp, pp + 4) *)
Ltac hw10p_kwr :=
  intros ? (rg & Hr & Hrb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end;
  repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; lia |]);
  destruct Hr.

(* the In facts of the top word's chunks *)
Ltac hw10p_in := repeat first [left; reflexivity | right].

(* the write windows of an entry state: the top size word at pp (atom 32), the rest read-only *)
Ltac hw10p_awr E pp U32 Hinp Hfresh :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end;
  eapply (hw10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 32%nat pp pp);
  [reflexivity | exact U32 | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | awr_ok_tac].

Print Assumptions hw10p_leaf.
Print Assumptions hw10p_HS_lem.
Print Assumptions hw10p_fin_lem.
