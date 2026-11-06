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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module names changed; 714 of its 754 lines of code are new or changed and 250 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostCorr.v at da027552bb80; restated for
   reac-pw/fuzz_rate's image A: role's cut pcs become rate's (R 0x82808, RT 0x82888), its registers rate's
   (s2 = K is atom 18, s7 = &pp->len atom 23, s6 its shadow address atom 22, s11 = pp atom 27), the shadow-base
   atom of the token engine is W10Bx = SOff 18 0, the rm_ / rl_ vocabulary becomes rtm_ / rt_, lib/A/RtPgSteps.v's
   helpers (rts_wx, rts_segs_low, same_io_wvb, rts_region_nth, rts_chunks, regs_kept_of_st_ok) stand in for role's
   RPgW7bBase and RPgCfgChanges, and the input byte at the cut comes from the lane kit's w10_input_now. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPostCorr.v, with its module paths, module names, addresses and numbers changed; 221 of its 797 lines of code are new or changed and 178 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostCorr.v at da027552bb80; restated for
   reac-pw/fuzz_rate's image A: role's cut pcs become rate's (R 0x82808, RT 0x82888), its registers rate's
   (s2 = K is atom 18, s7 = &pp->len atom 23, s6 its shadow address atom 22, s11 = pp atom 27), the shadow-base
   atom of the token engine is W10Bx = SOff 18 0, the rm_ / rl_ vocabulary becomes rtm_ / rt_, lib/A/RtPgSteps.v's
   helpers (rts_wx, rts_segs_low, same_io_wvb, rts_region_nth, rts_chunks, regs_kept_of_st_ok) stand in for role's
   RPgW7bBase and RPgCfgChanges, and the input byte at the cut comes from the lane kit's w10_input_now. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPostCorr.v at 8af9cea6f917; restated for
   image B (fuzz_rate.asan-ubsan) over lib/AU's RtPgMemB / RtPgSegB / RtPgStepsB / RtPgPostKB under the prefix
   wb10c_: image B's loop (R 0x82960, RT 0x829fc), its registers (t2 = &pp->len atom 7, s4 = K atom 20, a6 = 1
   atom 16, the loaded length in a7), pp, ~pp and the shadow address of &pp->len read from the real-frame cells
   R+0x168 / R+0x108 / R+0x170 (two read-only regions of s1 = R, atom 9; pp and ~pp are the extra atoms 36 / 37),
   and its three UBSan trap branches (0x82980, 0x829ac, 0x829b4), which the engine decides itself from closed-numeral
   atom ranges and one cond fact; the cuts' value lists carry R+0x108 and a6, and the input lies apart from the two
   cell ranges. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPostCorrB.v at db4fc362bebf for
   reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role and the segments
   lib/AU/Img0.v rsegs; RtPgMemB / RtPgSegB / RtPgStepsB / RtPgPostKB become RPgMem / RPgSeg / RPgSteps / RPgPostK
   (rtmb_ -> rm_, rsb_ -> rs_, rtsb_ -> rl_, rt_ -> rl_, q_X -> e_X, wb10_ -> w10_, wb10c_ -> w10c_); rate B's loop
   (R 0x82960, RT 0x829fc) becomes role B's (R 0x8209c, RT 0x82134), its trap branches 0x82980 / 0x829ac / 0x829b4
   become 0x820bc / 0x820e8 / 0x820f0; &pp->len is s6 (atom 22) in place of t2 (atom 7), pp is t2 (atom 7) in place
   of the cell R+0x168 (atom 36), ~pp and the shadow address of &pp->len are the cells R+0xf8 / R+0x148 in place of
   R+0x108 / R+0x170 (~pp is the extra atom 36), K is s11 (atom 27) in place of s4 (atom 20); the real frame is 0x200
   and the input lies apart from the one write range [R+0x48, R+0x160) of hi_w1 that holds both cells. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): one turn of the corruption
   loop of LLVMFuzzerTestOneInput (0x80020), pod.h:445-446 with fuzz.h:39-42. Proves no function (kind: segment
   lemma).
   THE CODE (the cut R = 0x8209c is the loop head; a3 = kk, a2 = cnt - kk, a4 = off, a0 the cursor, a5 what is
   left of the input, a6 = 1, t2 = pp, s6 = &pp->len)
     0x8209c ld a1,0x148(s1) / lbu a1,0(a1) / bnez a1 -> 0x829ec   the instrumented check of the 8-byte load of
                                                                   pp->len (R+0x148 holds ((pp + 0x4000) >> 3) + K;
                                                                   0x829ec / 0x829f0 is its error path)
     0x820a8 ld a7,0(s6) / add a1,a4,a3                 len, off + kk
     0x820b0 bgeu a1,a7 -> 0x82134                      off + kk >= len: the corruption ends (RT)
     0x820b4 beqz a5 -> 0x820e0                         no input left: the byte is 0 (0x820e0 li a7,0)
     0x820b8 addi t0,a0,1 / bgeu a6,t0 -> 0x82604       UBSan: the cursor + 1 does not wrap (a6 = 1)
     0x820c0 .. 0x820cc                                 the instrumented check of the 1-byte read at a0 (second test
                                                        0x82128 / 0x8212c, error path 0x82130)
     0x820d0 lbu a7,0(a0) / addi a5,a5,-1 / mv a0,t0 / j 0x820e4
     0x820e4 srli t0,a1,14 / bnez t0 -> 0x82604         UBSan: off + kk < 16384
     0x820ec ld t0,0xf8(s1) / bltu t0,a1 -> 0x82604     UBSan: ~pp is not below off + kk (pp + off + kk < 2^64)
     0x820f4 add a1,t2,a1                               pp + off + kk
     0x820f8 .. 0x82104                                 the instrumented check of the 1-byte store at a1 (second
                                                        test 0x8211c / 0x82120, error path 0x82124 -> 0x82a78)
     0x82108 sb a7,0(a1) / addi a2,a2,-1 / addi a3,a3,1
     0x82114 bnez a2 -> 0x8209c                         the next turn (R with kk + 1)
     0x82118 j 0x82134                                  the count is done (RT)
   The target 0x82604 of the three trap branches is an `unimp` word.
   The engine meets the two computed addresses through the facts' aliases: off + kk is atom 33 and pp + off + kk
   atom 34, so the store lands in a region of its own; each access's shadow bytes are a shadow entry of the engine
   (the length word and the store target inside the first block, the input byte inside the input), so no check
   reaches its error path. The engine decides the three trap branches itself: 0x820bc and 0x820f0 from the atom
   ranges (the cursor in [1, 2^47 - 2] against a6 in [1, 1]; ~pp in [2^63, 2^64 - 1] against off + kk in
   [8, 5440]), 0x820e8 from the cond fact (off + kk) >> 14 = 0 (w10c_shr14) that the state carries from the start,
   the method of RPgStepsU.rl_trap_820e8 (its decision procedure settles an equality only through the state's
   conds).
   w10_corr: RPgSeg's rs_piece_W10_corr_stmt, R kk -> R (kk + 1) or RT. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgMem RPgSeg RPgSteps RPgPostK.
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

(* ---- the input byte at the cursor ---- *)
Lemma w10c_nth_skipn : forall (rest : list byte) j x r1, skipn j rest = x :: r1 ->
  nth j (rs_u8s rest) 0 = bv_unsigned x.
Proof.
unfold rs_u8s. induction rest as [|y rest IH]; intros [|j] x r1 H; cbn in H |- *; try discriminate.
- injection H as -> ->. reflexivity.
- exact (IH j x r1 H).
Qed.

(* the sum of two atoms, as the engine writes `add` *)
Lemma w10c_den_add : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> 0 <= v1 < 2 ^ 62 ->
  ew E n2 = Z_to_bv 64 v2 -> 0 <= v2 < 2 ^ 62 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (v1 + v2).
Proof.
intros E n1 n2 v1 v2 H1 B1 H2 B2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)). cbn [zalu_raw].
apply zcanon_id. unfold M64. lia.
Qed.

(* the shadow entry of one input byte *)
Lemma w10c_shent_in : forall E m n src left c, amem_range src left -> U E W10Bx = SHADOW_OFF ->
  U E (SOff n 0) = c -> src <= c -> c + 1 <= src + left ->
  range_addressable (rd_of rsegs m) SHADOW_OFF c 1 ->
  shent_ok rsegs W10Bx E m (mkSHE n 0 1).
Proof.
intros E m n src left c Ham HB Hc H1 H2 Hra. split; cbn [she_m she_lo she_hi].
- rewrite HB, Hc. eapply range_addressable_sub; [exact Hra | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite HB. rewrite Hc in Ha.
  change (Z.min 0 1) with 0 in Ha. change (Z.max 0 1) with 1 in Ha.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* a nonempty suffix: its head is the next byte of the prefix *)
Lemma w10c_skipn_cons : forall (l : list byte) k y l', skipn k l = y :: l' ->
  firstn (S k) l = firstn k l ++ [y] /\ skipn (S k) l = l'.
Proof.
induction l as [|z l IH]; intros [|k] y l' H; cbn in H |- *; try discriminate.
- injection H as -> ->. split; reflexivity.
- destruct (IH k y l' H) as [H1 H2]. split; [rewrite H1; reflexivity | exact H2].
Qed.

Lemma w10c_le1 : forall y : byte, Z_to_le_bytes 1 (bv_unsigned y) = [y].
Proof. intros y. cbn [Z_to_le_bytes]. rewrite w10_byte_self. reflexivity. Qed.

(* the 64-bit complement as the cell R+0xf8 holds it, as an unsigned value *)
Lemma w10c_lnot_mod : forall p, 0 <= p < 2 ^ 64 -> Z.lnot p mod 2 ^ 64 = 2 ^ 64 - 1 - p.
Proof.
intros p Hp. replace (Z.lnot p) with ((2 ^ 64 - 1 - p) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* the UBSan test of 0x820e8 (`srli t0,a1,14; bnez t0`, pod.h:446) as a cond fact of the state: the engine settles an
   equality only through f_conds (YP0m decide_eq has no rule for a range of one value), so the state carries
   (off + kk) >> 14 = 0, and the engine then decides the trap branch not taken by itself *)
Lemma w10c_shr14 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 16384 ->
  acond_ok E (mkAC BC_EQ (SAlu ALU_SRL (SOff n 0) (SLit 14)) (SLit 0)).
Proof.
intros E n v Hn Hv. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_eq_U, U_SAlu, !U_SLit, (U_atom E n v Hn ltac:(lia)). cbn [zalu_raw].
change (Z.land (zcanon 14) 63) with 14. rewrite Z.shiftr_div_pow2 by lia.
rewrite Z.div_small by (change (2 ^ 14) with 16384; lia). apply Z.eqb_refl.
Qed.

(* the real-frame range of the build's write set (role_himg_B's hi_w1) that holds both cells the loop reads: the input
   lies outside it, so the two read-only cell regions of the loop's state are apart from the input byte's *)
Lemma w10c_not_w1 : forall e a, ~ rl_inw e (hi_w1 role_himg_B) a ->
  ~ (e_R e + 0x48 <= a < e_R e + 0x160).
Proof.
intros e a H Ha. apply H. unfold rl_inw. cbn [hi_w1 role_himg_B].
do 3 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rl_xv]. lia.
Qed.

(* a one-byte field of a region of a run's end state *)
Lemma w10c_field1 : forall {fx : YK11.FPState} E ss ms (H : word -> bool) i n lo hi wlo whi cs b e v,
  st_ok rsegs E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk 0 (CVal 1 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
  val_mem rsegs (mrestrict H (ms_mem ms)) b 1 v.
Proof.
intros fx E ss ms H i n lo hi wlo whi cs b e v HS Hi Hn Hc He Hv.
pose proof (rl_region_nth E ss ms i _ H HS Hi) as Hr.
pose proof (rl_chunks E (mrestrict H (ms_mem ms)) n b cs lo hi wlo whi Hr Hn _ Hc) as Hck.
replace b with (b + 0) by lia.
exact (val_of_chunk_ok rsegs E (mrestrict H (ms_mem ms)) b 0 1%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* the block after the store of the corruption's byte kk *)
Lemma w10c_img_next : forall {fx : YK11.FPState} {rc : YM05.RunCeil}
  (cx : rs_scx rsegs) W2 mem2 mem3 sh ps off bs kk (y : byte),
  rs_wf sh ps -> 8 <= off -> (kk < length bs)%nat -> off + Z.of_nat (length bs) <= rs_plen sh ps ->
  rs_pp_at rsegs cx W2 mem2 (rs_img_corr sh ps off bs (Z.of_nat kk)) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  firstn (S kk) bs = firstn kk bs ++ [y] ->
  rs_pp_at rsegs cx W2 mem3 (rs_img_corr sh ps off bs (Z.of_nat (S kk))).
Proof.
intros fx rc cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hk Hob Hpp Hv HK Hfs.
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
unfold rs_plen in Hob.
unfold rs_pp_at, rs_img_corr in *. rewrite Nat2Z.id in *. rewrite Hfs.
assert (Hl : length (firstn kk bs) = kk) by (rewrite length_firstn; lia).
rewrite <- (w10_img_step sh ps off (firstn kk bs) y ltac:(lia) ltac:(rewrite Hl; lia)).
rewrite Hl. rewrite <- (w10c_le1 y).
set (IMG := pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (firstn kk bs))
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
  (ents (PodRec sh ps None)) false) in *.
assert (HLl : Z.of_nat (length IMG) = PP_SIZE).
{ apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia | rewrite Hl; lia]. }
unfold PP_SIZE in HLl.
apply (rm_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem3 (e_pp (x_e cx)) _ (Z.to_nat off + kk) 1 (bv_unsigned y) Hpp).
- replace (e_pp (x_e cx) + Z.of_nat (Z.to_nat off + kk)) with (e_pp (x_e cx) + off + Z.of_nat kk) by lia. exact Hv.
- lia.
- intros z Hz Hn. apply HK; [unfold PP_SIZE; lia | lia].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* What one turn of the loop leaves, read off the turn's end: the journal clauses, the post cuts' values (with the
   R list's cell R+0xf8, a6 and t2), the frame's shadow and the block with one more corruption byte. *)
Lemma w10c_turn_common : forall (cx : rs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rs_pre rsegs B cx ->
  rs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 22; 23; 16; 7] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 /\
  rs_at_cx rsegs cx W2 mem3 regs3 (rs_L_post rsegs cx) /\
  rl_at rsegs (w_H W2) mem3 regs3 (x_e cx) (LCell XR 0xf8) (Z.lnot (e_pp (x_e cx))) /\
  getr regs3 (Z_to_bv 5 16) = w64 1 /\
  getr regs3 (Z_to_bv 5 7) = w64 (e_pp (x_e cx)) /\
  rs_fsh_at rsegs cx W2 mem3 rs_P0 /\
  rs_pp_at rsegs cx W2 mem3 (rs_img_corr sh ps off bs (Z.of_nat (S kk))) /\
  (kk < length bs)%nat /\ skipn (S kk) bs = fst (fuzz_u8s (length bs - S kk) r').
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
destruct (w10_R_bounds B cx HP) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7 & RB8).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
pose proof Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin). unfold rs_plen in Hob, Hbmin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hkl : (kk < length bs)%nat).
{ destruct (Nat.lt_ge_cases kk (length bs)) as [H|H]; [exact H|]. rewrite skipn_all2 in Hsk by exact H. discriminate. }
destruct (w10c_skipn_cons bs kk y _ Hsk) as [Hfs Hss].
assert (Hnp : forall a, e_R (x_e cx) - T_SEG_STK <= a -> a <> e_pp (x_e cx) + off + Z.of_nat kk).
{ intros a Ha. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hcell : forall o i, 0 <= o < 0x200 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) mem3 (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold T_SEG_STK, ASTACK in *; lia | apply Hnp; unfold T_SEG_STK, ASTACK; lia]. }
pose proof HL as HLx. unfold rs_at_cx, rs_at in HLx. apply Forall_app in HLx. destruct HLx as [HLp HLt].
apply Forall_cons_iff in HLt as [Hf8 HLt].
do 5 (apply Forall_cons_iff in HLt as [_ HLt]).
apply Forall_cons_iff in HLt as [H16 HLt].
apply Forall_cons_iff in HLt as [H7 _].
cbn [fst snd] in Hf8. cbn [fst snd rl_at] in H16, H7.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Hkl | exact Hss]]]]]]]].
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    (fun a => a = e_pp (x_e cx) + off + Z.of_nat kk) HC HJ3).
  + intros rr Hr. apply Hregs. destruct Hr as [->|[->| ->]]; cbn; tauto.
  + exact Hio3.
  + intros a Ha Hn. exact (HK a Ha Hn).
  + intros a ->. right. unfold PP_SIZE. lia.
- apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ HLp).
  intros f Hf. unfold rs_L_post in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
    first [ (apply Hregs; cbn; tauto) | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rm_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ _ Hf8).
  cbn [rm_keeps rl_xv]. intros i Hi. apply Hcell; lia.
- rewrite (Hregs 16 ltac:(cbn; tauto)). exact H16.
- rewrite (Hregs 7 ltac:(cbn; tauto)). exact H7.
- apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (e_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. change (Z.of_nat (length rs_P0)) with 88 in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  pose proof (w10_shadow_not_pp (e_pp (x_e cx)) (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | unfold PP_SIZE in Hs; lia].
- apply (w10c_img_next cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hkl Hob Hpp Hv); [| exact Hfs].
  intros a Ha Hn. apply HK; [unfold PP_SIZE in Ha; lia | exact Hn].
Qed.

Lemma w10c_finish_R : forall (cx : rs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rs_pre rsegs B cx ->
  rs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 22; 23; 16; 7] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rs_suffix rest r' ->
  getr regs3 (Z_to_bv 5 13) = w64 (Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 14) = w64 off ->
  getr regs3 (Z_to_bv 5 10) = w64 (rs_cur rsegs cx rest r') ->
  getr regs3 (Z_to_bv 5 15) = w64 (Z.of_nat (length r')) ->
  Z.of_nat (S kk) < cnt ->
  rs_cut_R rsegs B MT cx sh ps rest r' off bs cnt (Z.of_nat (S kk)) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  R13 R12 R14 R10 R15 Hlt.
destruct (w10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & Hf8 & H16 & H7 & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
split; [exact Hcore|]. split.
{ unfold rs_at_cx, rs_at in *. apply Forall_app. split; [exact HLp|].
  apply Forall_cons; [exact Hf8|].
  repeat (apply Forall_cons; [cbn [fst snd rl_at]; assumption |]). apply Forall_nil. }
split; [exact Hfsh|]. split; [exact Hpp|]. split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|].
split; [exact Hlen|]. split; [exact Htie|]. split; [exact Hcw|]. split; [lia|]. split; [lia|].
rewrite Nat2Z.id. exact Hss.
Qed.

Lemma w10c_finish_RT : forall (cx : rs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rs_pre rsegs B cx ->
  rs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 22; 23; 16; 7] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rs_suffix rest r' ->
  length bs = S kk ->
  rs_cut_RT rsegs B MT cx sh ps off bs rest r' ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  Hbl.
destruct (w10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & _ & _ & _ & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
destruct Hcw as (Hoff & Hob & Hb7 & _).
split; [exact Hcore|]. split; [exact HLp|]. split; [exact Hfsh|]. split; [rewrite Hbl; exact Hpp|].
split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Htie|].
split; [exact Hoff|]. split; [exact Hob | exact Hb7].
Qed.

Theorem w10_corr : rs_piece_W10_corr_stmt rsegs B MT.
Proof.
unfold rs_piece_W10_corr_stmt. intros cx POST rest kk Hst HR1 HRT.
unfold rs_from_R. intros ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt HR.
destruct Hst as (HP & Hfsh0 & _ & _).
pose proof HR as HRc.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
destruct (w10_R_bounds B cx HP) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7 & RB8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
destruct Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin).
unfold rs_plen in Hob, Hbmin.
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & Hindisj).
destruct Hsuf as (j & Hj & Hrj).
set (pp := e_pp (x_e cx)) in *.
set (Lp := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
set (enc := pod_encode (PodRec sh ps None)) in *.
rewrite Nat2Z.id in Hskip.
assert (Hbl : length (overwrite enc (Z.to_nat off) (firstn kk bs)) = length (pc_buf (PbCut sh ps None))).
{ rewrite length_overwrite; [exact HW2|]. rewrite length_firstn. lia. }
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 Lp).
{ unfold rs_pp_at, rs_img_corr in Hpp. rewrite Nat2Z.id in Hpp.
  pose proof (rm_pp_len rsegs (overwrite enc (Z.to_nat off) (firstn kk bs)) _ _ _ _ _
    ltac:(rewrite Hbl; unfold POD_BUF_MAX; lia) HW3 HW4 (w_H W2) mem2 pp Hpp) as X.
  rewrite Hbl in X. exact X. }
pose proof HL as HL0.
unfold rs_at_cx, rs_at, rs_L_post in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P27 & P22 & P23 & C18 & C20 & C40 & C38 & Ce8 & Cc0 & C120 & C140 & C148 &
  Cf8 & P13 & P12 & P14 & P10 & P15 & P16 & P7 & _).
cbn [fst snd rl_at] in P8, P9, P19, P27, P22, P23, P13, P12, P14, P10, P15, P16, P7.
cbn [fst snd rl_at rl_xv] in Cf8, C148.
pose proof HC as (HJ & _).
change (e_pp (x_e cx)) with pp in P22, C148.
set (cur := rs_cur rsegs cx rest r) in P10.
assert (Hcur : cur = e_src (x_e cx) + Z.of_nat j).
{ subst cur. unfold rs_cur. rewrite Hrj, length_skipn. lia. }
assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Hrj, length_skipn; lia).
assert (HK47 : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
set (src := e_src (x_e cx)) in Hcur, HK47, Hamr, Hsrc0, Hsrc63, Hindisj.
set (kz := Z.of_nat kk) in P13, P12, Hkk, Hkb, Hpp.
(* the two real-frame cells the loop reads, as unsigned values *)
assert (Hpp47 : 0 <= pp + 0x4000 < 2 ^ 47) by lia.
assert (Hsa : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia)).
  assert ((pp + 0x4000) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite (Z.mod_small (shadow_addr (pp + 0x4000))) in C148 by exact Hsa.
rewrite (w10c_lnot_mod pp ltac:(lia)) in Cf8.
remember (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end);
  Z_to_bv 64 (2 ^ 64 - 1 - pp)]) as E eqn:HE.
assert (E7 : ew E 7 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact P7).
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E10 : ew E 10 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact P10).
assert (E12 : ew E 12 = Z_to_bv 64 (cnt - kz)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 (Z_to_bv 5 12) eq_refl); exact P12).
assert (E13 : ew E 13 = Z_to_bv 64 kz) by (subst E; rewrite (ew_Ereg_nat regs2 _ 13 (Z_to_bv 5 13) eq_refl); exact P13).
assert (E14 : ew E 14 = Z_to_bv 64 off) by (subst E; rewrite (ew_Ereg_nat regs2 _ 14 (Z_to_bv 5 14) eq_refl); exact P14).
assert (E15 : ew E 15 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 15 (Z_to_bv 5 15) eq_refl); exact P15).
assert (E16 : ew E 16 = Z_to_bv 64 1) by (subst E; rewrite (ew_Ereg_nat regs2 _ 16 (Z_to_bv 5 16) eq_refl); exact P16).
assert (E22 : ew E 22 = Z_to_bv 64 (pp + 0x4000)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 22 (Z_to_bv 5 22) eq_refl); exact P22).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E32 : ew E 32 = Z_to_bv 64 Lp) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pp + off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end))
  by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (2 ^ 64 - 1 - pp)) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (HB : U E W10Bx = SHADOW_OFF) by exact (w10_U_atom E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)).
assert (HoffL : off + kz <= Lp) by lia.
pose proof HL0 as HLpost. unfold rs_at_cx, rs_at in HLpost. apply Forall_app in HLpost. destruct HLpost as [HLpost _].
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end);
  Z_to_bv 64 (2 ^ 64 - 1 - pp)]) E)
  by (rewrite HE; split; [intros; reflexivity | reflexivity]).
assert (Himgl : forall k, (k <= length bs)%nat -> Z.of_nat (length (rs_img_corr sh ps off bs (Z.of_nat k))) = PP_SIZE).
{ intros k Hk. unfold rs_img_corr. fold enc. apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
(* the regions every state of the turn starts with: the length word (s6), the two real-frame cells (s1) *)
assert (HRL : region_ok rsegs E (mrestrict (w_H W2) mem2)
  (YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))])).
{ apply (rm_ro_region rsegs E (w_H W2) mem2 22 (pp + 0x4000)).
  - rewrite E22. rewrite unsigned_lit_small by lia. reflexivity.
  - lia. - lia.
  - constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (pp + 0x4000) 0 8 (SOff 32 0) Lp).
    + exact (w10_den_atom _ 32 Lp E32). + cbn. lia. + cbn. lia. + rewrite Z.add_0_r. exact HLv. }
assert (HRA : region_ok rsegs E (mrestrict (w_H W2) mem2)
  (YP09.mkRegion (Some 9%nat) 0xf8 0x100 0 0 [YP09.mkChunk 0xf8 (CVal 8 (SOff 36 0))])).
{ apply (rm_ro_region rsegs E (w_H W2) mem2 9 (e_R (x_e cx))).
  - rewrite E9. rewrite unsigned_lit_small by lia. reflexivity.
  - lia. - lia.
  - constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0xf8 8 (SOff 36 0) (2 ^ 64 - 1 - pp)).
    + exact (w10_den_atom _ 36 _ E36). + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. + cbn. lia.
    + exact Cf8. }
assert (HRB : region_ok rsegs E (mrestrict (w_H W2) mem2)
  (YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0
    [YP09.mkChunk 0x148 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 27 0)))])).
{ apply (rm_ro_region rsegs E (w_H W2) mem2 9 (e_R (x_e cx))).
  - rewrite E9. rewrite unsigned_lit_small by lia. reflexivity.
  - lia. - lia.
  - constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0x148 8 _ (shadow_addr (pp + 0x4000))).
    + exact (w10_den_sh E 22 27 (pp + 0x4000) E22 Hpp47 E27).
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. + cbn. lia.
    + exact C148. }
destruct (Z_le_gt_dec Lp (off + kz)) as [Hge|Hlt].
{ (* off + kk reaches the length: the corruption ends with the bytes written so far *)
  assert (Hkbs : kz = Z.of_nat (length bs)) by lia.
  assert (HS : st_ok rsegs E (mkSS 0x8209c sr_atoms
    [YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
     YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0
       [YP09.mkChunk 0x148 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 27 0)))]] None
    (mkFacts [(22%nat, mkAF 4096 W10_HI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
              (33%nat, mkAF 8 5447 0); (12%nat, mkAF 1 7 0); (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
       [mkAC BC_GEU (SOff 33 0) (SOff 32 0)]
       [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0)]))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x8209c) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [exact HRL | constructor; [exact HRB | constructor]].
    - apply pairwise_disjoint_of_extents.
      cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
      cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
      rewrite E22, E9, !unsigned_lit_small by lia.
      unfold T_SEG_STK, ASTACK in *. repeat split; lia.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
      refine (conj _ (conj (conj _ I) (conj _ I))).
      + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E22, E27, E32, E33, E12, E13, E14.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
        repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
        try (rewrite Z.pow_0_r; apply Z.mod_1_r).
        change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
      + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
        apply negb_true_iff, Z.ltb_ge. lia.
      + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia. }
  assert (SHOK : sh_ok rsegs W10Bx [mkSHE 22 0 8] E (mrestrict (w_H W2) mem2)).
  { constructor; [|constructor].
    apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 22 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 22 _ E22 ltac:(lia)); lia. }
  unfold cfg_at. change (w64 RS_R) with (Z_to_bv 64 0x8209c).
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82134.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; lia. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 11; Z_to_bv 5 17] HS HAE ltac:(vm_compute; reflexivity)) as RK.
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
      apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
    + apply same_io_wvb.
    + intros a Ha _. exact (HK a Ha).
    + intros a [].
  - apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HLpost).
    intros f Hf. unfold rs_L_post in Hf. cbv zeta in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
      first [ (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
            | (intros i Hi; apply HK; lia) ] |]).
    destruct Hf.
  - apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) rs_P0 Hfsh).
    intros i Hi. apply HK. change (Z.of_nat (length rs_P0)) with 88 in Hi.
    pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF. lia.
  - rewrite <- Hkbs. apply (rm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) pp _ Hpp).
    assert (X : Z.of_nat (length (rs_img_corr sh ps off bs kz)) = PP_SIZE) by exact (Himgl kk ltac:(lia)).
    intros y Hy. rewrite X in Hy. apply HK. unfold PP_SIZE in Hy. lia.
  - exact Hin.
  - exists j. split; [exact Hj | exact Hrj].
  - exact Hwf.
  - exact Hlen.
  - exact Htie.
  - exact Hoff.
  - unfold rs_plen. exact Hob.
  - exact Hb7. }
(* the store's region inside the first block *)
assert (HRS34 : region_ok rsegs E (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some 34%nat) 0 1 0 1 [])).
{ apply (rm_rw_region rsegs _ (w_H W2) mem2 34 (pp + off + kz)).
  - rewrite E34. rewrite unsigned_lit_small by lia. reflexivity.
  - lia. - lia.
  - intros o Ho. apply Hpres. lia.
  - constructor. }
destruct r as [|x r1].
{ (* no input left: the byte is 0 *)
  cbv beta iota in E35, HE, HAE.
  assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
  assert (Hsk : skipn kk bs = Z_to_bv 8 0 :: fst (fuzz_u8s (length bs - S kk) [])).
  { rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply w10_fuzz_u8s_nil. }
  assert (Hsuf' : rs_suffix rest []) by (exists j; split; [exact Hj | exact Hrj]).
  assert (Hy0 : bv_unsigned (Z_to_bv 8 0 : byte) = 0) by reflexivity.
  change (Z.of_nat (length (@nil byte))) with 0 in E15.
assert (HS : st_ok rsegs E (mkSS 0x8209c sr_atoms
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 9%nat) 0xf8 0x100 0 0 [YP09.mkChunk 0xf8 (CVal 8 (SOff 36 0))];
   YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0
     [YP09.mkChunk 0x148 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 27 0)))]] None
  (mkFacts [(22%nat, mkAF 4096 W10_HI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 W10_HI 0);
            (36%nat, mkAF 9223372036854775808 18446744073709551615 0);
            (15%nat, mkAF 0 0 0); (12%nat, mkAF 1 7 0);
            (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
     [mkAC BC_LTU (SOff 33 0) (SOff 32 0); mkAC BC_EQ (SOff 15 0) (SLit 0);
      mkAC BC_EQ (SAlu ALU_SRL (SOff 33 0) (SLit 14)) (SLit 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 7 0) (SOff 33 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x8209c) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HRS34 | constructor; [exact HRL | constructor; [exact HRA | constructor; [exact HRB | constructor]]]].
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
    rewrite E34, E22, E9, !unsigned_lit_small by lia.
    unfold T_SEG_STK, ASTACK in *. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ (conj _ (conj _ I))) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E22, E27, E32, E33, E34, E36, E15, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (w10_U_atom _ 15 0 E15 ltac:(lia)), U_lit by lia.
      reflexivity.
    + exact (w10c_shr14 _ 33 (off + kz) E33 ltac:(lia)).
    + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (w10c_den_add _ 7 33 pp (off + kz) E7 ltac:(lia) E33 ltac:(lia)), (w10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the store target and the length word inside the first block *)
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 34 0 1; mkSHE 22 0 8] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 22 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 22 _ E22 ltac:(lia)); lia. }
unfold cfg_at. change (w64 RS_R) with (Z_to_bv 64 0x8209c).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82134.
{ cbn [ss_mem].
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
  { rewrite E34. apply unsigned_lit_small. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_nil. }
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok w10_tbl_ok HS SHOK W10Bspan.
- (* a2 - 1 <> 0: the next turn *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x8209c.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
  { rewrite Hy0.
    apply (w10c_field1 _ _ ms (w_H W2) 0%nat 34%nat 0 1 0 1 _ (pp + off + kz) (SLit 0) 0 HS eq_refl);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity | reflexivity | lia ]. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 17]
    HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 22; 23; 16; 7] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity] |]).
    destruct Hn. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 13) HS). w10_sr_eval.
    rewrite (w10_den_off _ 13 kz 1) by (rewrite !ew_ewset_other by lia; exact E13).
    f_equal. unfold kz. lia. }
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 12) HS). w10_sr_eval.
    rewrite (w10_den_off _ 12 (cnt - kz) (-1)) by (rewrite !ew_ewset_other by lia; exact E12).
    f_equal. unfold kz. lia. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
  { rewrite RK; [exact P14 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (rs_cur rsegs cx rest [])).
  { rewrite RK; [exact P10 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length (@nil byte)))).
  { rewrite RK; [exact P15 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps [] off bs cnt).
  apply (w10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] [] (Z_to_bv 8 0)
    HP HRc HJ ltac:(eapply same_io_trans; apply same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82134.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
  { rewrite Hy0.
    apply (w10c_field1 _ _ ms (w_H W2) 0%nat 34%nat 0 1 0 1 _ (pp + off + kz) (SLit 0) 0 HS eq_refl);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity | reflexivity | lia ]. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 17]
    HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 22; 23; 16; 7] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs []).
  exact (w10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] [] (Z_to_bv 8 0)
    HP HRc HJ ltac:(eapply same_io_trans; apply same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
}
cbv beta iota in E35, HE, HAE.
assert (Hjr : (j < length rest)%nat) by (cbn [length] in Hrl; lia).
assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
assert (Hsk : skipn kk bs = x :: fst (fuzz_u8s (length bs - S kk) r1)).
{ rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply w10_fuzz_u8s_cons. }
assert (Hsuf' : rs_suffix rest r1).
{ exists (S j). split; [lia | symmetry; exact (proj2 (w10c_skipn_cons rest j x r1 (eq_sym Hrj)))]. }
destruct (w10_input_now B MT cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat j) HP Hin Hfsh0 HC Hfsh ltac:(lia))
  as (Hbyte & Hra).
assert (Hx : val_mem rsegs (mrestrict (w_H W2) mem2) cur 1 (bv_unsigned x)).
{ rewrite Nat2Z.id in Hbyte. rewrite (w10c_nth_skipn rest j x r1 (eq_sym Hrj)) in Hbyte.
  rewrite Hcur. exact Hbyte. }
pose proof (bv_unsigned_in_range _ x) as Hxr. unfold bv_modulus in Hxr. change (Z.of_N 8) with 8 in Hxr.
destruct (Hindisj cur ltac:(lia)) as (Hns & Hnw & Hnp). unfold PP_SIZE in Hnp.
pose proof (w10c_not_w1 (x_e cx) cur Hnw) as Hw1.
assert (HS : st_ok rsegs E (mkSS 0x8209c sr_atoms
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))];
   YP09.mkRegion (Some 9%nat) 0xf8 0x100 0 0 [YP09.mkChunk 0xf8 (CVal 8 (SOff 36 0))];
   YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0
     [YP09.mkChunk 0x148 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 27 0)))]] None
  (mkFacts [(22%nat, mkAF 4096 W10_HI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 W10_HI 0); (35%nat, mkAF 0 255 0);
            (36%nat, mkAF 9223372036854775808 18446744073709551615 0);
            (10%nat, mkAF 1 (2 ^ 47 - 2) 0); (15%nat, mkAF 1 (2 ^ 47) 0); (16%nat, mkAF 1 1 0);
            (12%nat, mkAF 1 7 0); (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
     [mkAC BC_LTU (SOff 33 0) (SOff 32 0); mkAC BC_EQ (SAlu ALU_SRL (SOff 33 0) (SLit 14)) (SLit 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 7 0) (SOff 33 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x8209c) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HRS34 | constructor; [exact HRL | constructor; [| constructor; [exact HRA | constructor; [exact HRB | constructor]]]]].
    apply (rm_ro_region rsegs _ (w_H W2) mem2 10 cur).
    + rewrite E10. rewrite unsigned_lit_small by lia. reflexivity.
    + lia. + lia.
    + constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 35 0) (bv_unsigned x)).
      * exact (w10_den_atom _ 35 _ E35). * cbn. lia. * cbn. lia. * rewrite Z.add_0_r. exact Hx.
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
    rewrite E34, E22, E10, E9, !unsigned_lit_small by lia.
    unfold T_SEG_STK, ASTACK in *. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ (conj _ I)) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E22, E27, E32, E33, E34, E35, E36, E10, E15, E16, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + exact (w10c_shr14 _ 33 (off + kz) E33 ltac:(lia)).
    + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (w10c_den_add _ 7 33 pp (off + kz) E7 ltac:(lia) E33 ltac:(lia)), (w10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the store target and the length word inside the first block, the input byte *)
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 34 0 1; mkSHE 22 0 8; mkSHE 10 0 1] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 22 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 22 _ E22 ltac:(lia)); lia.
  - apply (w10c_shent_in E _ 10 src (e_left (x_e cx)) cur Hamr HB (w10_U_atom E 10 _ E10 ltac:(lia)));
    [lia | lia | rewrite Hcur; exact Hra]. }
unfold cfg_at. change (w64 RS_R) with (Z_to_bv 64 0x8209c).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82134.
{ cbn [ss_mem].
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
  { rewrite E34. apply unsigned_lit_small. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok w10_tbl_ok HS SHOK W10Bspan.
- (* a2 - 1 <> 0: the next turn *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x8209c.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
        [|lia|lia|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
        [|lia|lia|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { apply (w10c_field1 _ _ ms (w_H W2) 0%nat 34%nat 0 1 0 1 _ (pp + off + kz) (SOff 35 0) (bv_unsigned x) HS eq_refl);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | apply (w10_den_atom _ 35); rewrite !ew_ewset_other by lia; exact E35
      | lia ]. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15;
     Z_to_bv 5 17] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 22; 23; 16; 7] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity] |]).
    destruct Hn. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 13) HS). w10_sr_eval.
    rewrite (w10_den_off _ 13 kz 1) by (rewrite !ew_ewset_other by lia; exact E13).
    f_equal. unfold kz. lia. }
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 12) HS). w10_sr_eval.
    rewrite (w10_den_off _ 12 (cnt - kz) (-1)) by (rewrite !ew_ewset_other by lia; exact E12).
    f_equal. unfold kz. lia. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
  { rewrite RK; [exact P14 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (rs_cur rsegs cx rest r1)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 10) HS). w10_sr_eval.
    rewrite (w10_den_off _ 10 cur 1) by (rewrite !ew_ewset_other by lia; exact E10).
    f_equal. unfold cur, rs_cur. cbn [length]. lia. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length r1))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 15) HS). w10_sr_eval.
    rewrite (w10_den_off _ 15 (Z.of_nat (length (x :: r1))) (-1)) by (rewrite !ew_ewset_other by lia; exact E15).
    f_equal. cbn [length]. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r1 off bs cnt).
  apply (w10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82134.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
        [|lia|lia|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
        [|lia|lia|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { apply (w10c_field1 _ _ ms (w_H W2) 0%nat 34%nat 0 1 0 1 _ (pp + off + kz) (SOff 35 0) (bv_unsigned x) HS eq_refl);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | apply (w10_den_atom _ 35); rewrite !ew_ewset_other by lia; exact E35
      | lia ]. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15;
     Z_to_bv 5 17] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 22; 23; 16; 7] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r1).
  exact (w10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
Qed.
End c.
