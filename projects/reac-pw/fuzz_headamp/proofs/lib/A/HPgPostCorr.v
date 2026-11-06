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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPostCorr.v, with its module paths, addresses and numbers changed; 229 of its 765 lines of code are new or changed and 218 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostCorr.v at 01f4363fe7d2, for reac-pw/fuzz_headamp
   image A: module paths, the rs_ / rl_ / rm_ prefixes renamed to hs_ / hd_ / hm_; the pcs moved to headamp's twins (R
   0x82018 -> 0x82da4, RT 0x82094 -> 0x82e2c); the post cuts' registers (F in s10, &pp->corrupt in s2, no pp register);
   local re-walk of the turn: the shadow check of pp->len in the `beqz a1,+8; j error` form, and pp read from R+0xf0
   into t0 on both arms of the byte (`ld t0,0xf0(s1)` 0x82dcc / 0x82de8, where role keeps pp in s11), so the store
   address pp + off + kk is aliased through the atom of that cell (atom 36) instead of s11's. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): one turn of the corruption loop of
   LLVMFuzzerTestOneInput (0x80bc0), pod.h:445-446 with fuzz.h:39-42. Proves no function (kind: segment lemma).
   THE CODE (the cut R = 0x82da4 is the loop head; a3 = kk, a2 = cnt - kk, a4 = off, a0 the cursor, a5 what is left
   of the input)
     0x82da4 lbu a1,0(s4) / beqz a1,+8 / j 0x83d84        the shadow byte of &pp->len (s4 = (pp + 0x4000 >> 3) + K)
     0x82db0 ld a6,0(s5) / add a1,a4,a3                  len, off + kk
     0x82db8 bgeu a1,a6 -> 0x82e2c                       off + kk >= len: the corruption ends (RT)
     0x82dbc beqz a5 -> 0x82de4                          no input left: the byte is 0 (0x82de4 mv a6,zero)
     0x82dc0 .. 0x82dd0                                  the check of the 1-byte read at a0 (slow test 0x82e20), with
                                                         `ld t0,0xf0(s1)` 0x82dcc between its load and its branch
     0x82dd4 lbu a6,0(a0) / addi a0,a0,1 / addi a5,a5,-1 / j 0x82dec
     0x82de4 mv a6,zero / 0x82de8 ld t0,0xf0(s1)          (the arm with no input left)
     0x82dec add a1,t0,a1                                pp + off + kk
     0x82df0 .. 0x82dfc                                  the check of the 1-byte store at a1 (slow test 0x82e14)
     0x82e00 sb a6,0(a1) / addi a2,a2,-1 / addi a3,a3,1
     0x82e0c bnez a2 -> 0x82da4                          the next turn (R with kk + 1)
     0x82e10 j 0x82e2c                                   the count is done (RT)
   The engine meets the two computed addresses through the facts' aliases: off + kk is atom 33, R+0xf0's cell (pp)
   is atom 36 and pp + off + kk atom 34, so the store lands in a region of its own; each access's shadow bytes are a
   shadow entry of the engine (the length word and the store target inside the first block, the input byte inside the
   input), so no check reaches its error path.
   w10_corr: the statement hs_piece_W10_corr_stmt (lib/A/HPgSeg.v), R kk -> R (kk + 1) or RT. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW7bBase HPgW6cKit HPgPostK.
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
Lemma w10c_nth_skipn : forall (rest : list byte) j x r1, skipn j rest = x :: r1 -> nth j (hd_zbytes rest) 0 = bv_unsigned x.
Proof.
unfold hd_zbytes. induction rest as [|y rest IH]; intros [|j] x r1 H; cbn in H |- *; try discriminate.
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
  range_addressable (rd_of rsegs m) SHADOW_OFF src left ->
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

(* the block after the store of the corruption's byte kk *)
Lemma w10c_img_next : forall (cx : hs_scx rsegs) W2 mem2 mem3 sh ps off bs kk (y : byte),
  hs_wf sh ps -> 8 <= off -> (kk < length bs)%nat -> off + Z.of_nat (length bs) <= hs_plen sh ps ->
  hs_pp_at rsegs cx W2 mem2 (hs_img_corr sh ps off bs (Z.of_nat kk)) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  firstn (S kk) bs = firstn kk bs ++ [y] ->
  hs_pp_at rsegs cx W2 mem3 (hs_img_corr sh ps off bs (Z.of_nat (S kk))).
Proof.
intros cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hk Hob Hpp Hv HK Hfs.
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
unfold hs_plen in Hob.
unfold hs_pp_at, hs_img_corr in *. rewrite Nat2Z.id in *. rewrite Hfs.
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
apply (hm_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem3 (e_pp (x_e cx)) _ (Z.to_nat off + kk) 1 (bv_unsigned y) Hpp).
- replace (e_pp (x_e cx) + Z.of_nat (Z.to_nat off + kk)) with (e_pp (x_e cx) + off + Z.of_nat kk) by lia. exact Hv.
- lia.
- intros z Hz Hn. apply HK; [unfold PP_SIZE; lia | lia].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* What one turn of the loop leaves, read off the turn's end: the journal clauses, the post cuts' values, the
   frame's shadow and the block with one more corruption byte. *)
Lemma w10c_turn_common : forall (cx : hs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
  hs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 26; 20; 18] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 /\
  hs_at_cx rsegs cx W2 mem3 regs3 (hs_L_post rsegs cx) /\
  hs_fsh_at rsegs cx W2 mem3 hs_P0 /\
  hs_pp_at rsegs cx W2 mem3 (hs_img_corr sh ps off bs (Z.of_nat (S kk))) /\
  (kk < length bs)%nat /\ skipn (S kk) bs = fst (fuzz_u8s (length bs - S kk) r').
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
pose proof Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin). unfold hs_plen in Hob, Hbmin.
destruct (hs_pre_geom rsegs B cx HP) as (_ & X1 & X2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hkl : (kk < length bs)%nat).
{ destruct (Nat.lt_ge_cases kk (length bs)) as [H|H]; [exact H|]. rewrite skipn_all2 in Hsk by exact H. discriminate. }
destruct (w10c_skipn_cons bs kk y _ Hsk) as [Hfs Hss].
assert (Hnp : forall a, e_R (x_e cx) - T_SEG_STK <= a -> a <> e_pp (x_e cx) + off + Z.of_nat kk).
{ intros a Ha. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hcell : forall o i, 0 <= o < 0x160 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) mem3 (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia | apply Hnp; unfold T_SEG_STK, ASTACK; lia]. }
split; [|split; [|split; [|split; [|split; [exact Hkl | exact Hss]]]]].
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (fun a => a = e_pp (x_e cx) + off + Z.of_nat kk) HC HJ3).
  + intros rr Hr. apply Hregs. destruct Hr as [->|[->| ->]]; cbn; tauto.
  + exact Hio3.
  + intros a Ha Hn. exact (HK a Ha Hn).
  + intros a ->. right. unfold PP_SIZE. lia.
- pose proof HL as HLp. unfold hs_at_cx, hs_at in HLp. apply Forall_app in HLp. destruct HLp as [HLp _].
  apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ HLp).
  intros f Hf. unfold hs_L_post in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv];
    first [ (apply Hregs; cbn; tauto) | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (e_F (x_e cx)) hs_P0 Hfsh).
  intros i Hi. change (length hs_P0) with 80%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  pose proof (w10_shadow_not_pp (e_pp (x_e cx)) (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | unfold PP_SIZE in Hs; lia].
- apply (w10c_img_next cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hkl Hob Hpp Hv); [| exact Hfs].
  intros a Ha Hn. apply HK; [unfold PP_SIZE in Ha; lia | exact Hn].
Qed.

Lemma w10c_finish_R : forall (cx : hs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
  hs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 26; 20; 18] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  hs_suffix rest r' ->
  getr regs3 (Z_to_bv 5 13) = w64 (Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 14) = w64 off ->
  getr regs3 (Z_to_bv 5 10) = w64 (hs_cur rsegs cx rest r') ->
  getr regs3 (Z_to_bv 5 15) = w64 (Z.of_nat (length r')) ->
  Z.of_nat (S kk) < cnt ->
  hs_cut_R rsegs B MT cx sh ps rest r' off bs cnt (Z.of_nat (S kk)) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  R13 R12 R14 R10 R15 Hlt.
destruct (w10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
split; [exact Hcore|]. split.
{ unfold hs_at_cx, hs_at in *. apply Forall_app. split; [exact HLp|].
  repeat (apply Forall_cons; [cbn [fst snd hd_at]; assumption |]). apply Forall_nil. }
split; [exact Hfsh|]. split; [exact Hpp|]. split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|].
split; [exact Hlen|]. split; [exact Htie|]. split; [exact Hcw|]. split; [lia|]. split; [lia|].
rewrite Nat2Z.id. exact Hss.
Qed.

Lemma w10c_finish_RT : forall (cx : hs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
  hs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 26; 20; 18] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  hs_suffix rest r' ->
  length bs = S kk ->
  hs_cut_RT rsegs B MT cx sh ps off bs rest r' ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  Hbl.
destruct (w10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
destruct Hcw as (Hoff & Hob & Hb7 & _).
split; [exact Hcore|]. split; [exact HLp|]. split; [exact Hfsh|]. split; [rewrite Hbl; exact Hpp|].
split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Htie|].
split; [exact Hoff|]. split; [exact Hob | exact Hb7].
Qed.

Theorem w10_corr : hs_piece_W10_corr_stmt rsegs B MT.
Proof.
unfold hs_piece_W10_corr_stmt. intros cx POST rest kk Hst HR1 HRT.
unfold hs_from_R. intros ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt HR.
destruct Hst as (HP & _ & _ & _).
pose proof HR as HRc.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
destruct Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin).
unfold hs_plen in Hob, Hbmin.
destruct (hs_in_now rsegs B MT cx rest hs_P0 ly2 S2 W2 regs2 mem2 md2 HP Hin HC Hfsh eq_refl) as (Hbytes & Hra & _).
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & Hindisj).
destruct Hsuf as (j & Hj & Hrj).
set (pp := e_pp (x_e cx)) in *.
set (Lp := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
set (enc := pod_encode (PodRec sh ps None)) in *.
rewrite Nat2Z.id in Hskip.
assert (Hbl : length (overwrite enc (Z.to_nat off) (firstn kk bs)) = length (pc_buf (PbCut sh ps None))).
{ rewrite length_overwrite; [exact HW2|]. rewrite length_firstn. lia. }
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 Lp).
{ unfold hs_pp_at, hs_img_corr in Hpp. rewrite Nat2Z.id in Hpp.
  pose proof (hm_pp_len rsegs (overwrite enc (Z.to_nat off) (firstn kk bs)) _ _ _ _ _
    ltac:(rewrite Hbl; unfold POD_BUF_MAX; lia) HW3 HW4 (w_H W2) mem2 pp Hpp) as X.
  rewrite Hbl in X. exact X. }
pose proof HL as HL0.
unfold hs_at_cx, hs_at, hs_L_post in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P23 & P21 & P26 & P20 & P18 & Q20 & Q28 & Q40 & Q90 & Qa0 & Q60 & Qf0 &
  P13 & P12 & P14 & P10 & P15 & _).
cbn [fst snd hd_at hd_xv] in P8, P9, P19, P23, P21, P26, P20, P18, P13, P12, P14, P10, P15, Qf0.
pose proof HC as (HJ & _).
change (e_pp (x_e cx)) with pp in P21, P20, P18, Qf0.
set (cur := hs_cur rsegs cx rest r) in P10.
assert (Hcur : cur = e_src (x_e cx) + Z.of_nat j).
{ subst cur. unfold hs_cur. rewrite Hrj, length_skipn. lia. }
assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Hrj, length_skipn; lia).
assert (HK47 : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
set (src := e_src (x_e cx)) in Hcur, HK47, Hamr, Hsrc0, Hsrc63, Hra, Hbytes, Hindisj.
set (kz := Z.of_nat kk) in P13, P12, Hkk, Hkb, Hpp.
remember (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end); Z_to_bv 64 pp]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E10 : ew E 10 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact P10).
assert (E12 : ew E 12 = Z_to_bv 64 (cnt - kz)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 (Z_to_bv 5 12) eq_refl); exact P12).
assert (E13 : ew E 13 = Z_to_bv 64 kz) by (subst E; rewrite (ew_Ereg_nat regs2 _ 13 (Z_to_bv 5 13) eq_refl); exact P13).
assert (E14 : ew E 14 = Z_to_bv 64 off) by (subst E; rewrite (ew_Ereg_nat regs2 _ 14 (Z_to_bv 5 14) eq_refl); exact P14).
assert (E15 : ew E 15 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 15 (Z_to_bv 5 15) eq_refl); exact P15).
assert (E21 : ew E 21 = Z_to_bv 64 (pp + 0x4000)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl); exact P21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E36 : ew E 36 = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (E32 : ew E 32 = Z_to_bv 64 Lp) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pp + off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end))
  by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (HB : U E W10Bx = SHADOW_OFF) by exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)).
assert (Hpp47 : 0 <= pp + 0x4000 < 2 ^ 47) by lia.
assert (HoffL : off + kz <= Lp) by lia.
pose proof HL0 as HLpost. unfold hs_at_cx, hs_at in HLpost. apply Forall_app in HLpost. destruct HLpost as [HLpost _].
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end); Z_to_bv 64 pp]) E)
  by (rewrite HE; split; [intros; reflexivity | reflexivity]).
assert (HRcell : forall o, 0 <= o -> o + 8 <= 0x160 -> pp + PP_SIZE <= e_R (x_e cx) + o).
{ intros o Ho1 Ho2. unfold T_SEG_STK, ASTACK, PP_SIZE in *. lia. }
assert (HRk : 0 <= e_R (x_e cx) - T_SEG_STK /\ e_R (x_e cx) + 0x1e0 <= 2 ^ 47).
{ destruct (hs_pre_geom rsegs B cx HP) as (_ & X1 & X2 & _). unfold kHighMemBeg in X1. lia. }
assert (HRnn : 0 <= e_R (x_e cx)) by (destruct HRk as [HRk1 _]; unfold T_SEG_STK, ASTACK in HRk1; lia).
assert (Himgl : forall k, (k <= length bs)%nat -> Z.of_nat (length (hs_img_corr sh ps off bs (Z.of_nat k))) = PP_SIZE).
{ intros k Hk. unfold hs_img_corr. fold enc. apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
destruct (Z_le_gt_dec Lp (off + kz)) as [Hge|Hlt].
{ (* off + kk reaches the length: the corruption ends with the bytes written so far *)
  assert (Hkbs : kz = Z.of_nat (length bs)) by lia.
  assert (HS : st_ok rsegs E (mkSS 0x82da4
    (sr_set sr_atoms (Z_to_bv 5 20) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)))
    [YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
    (mkFacts [(21%nat, mkAF 4096 W10_HI 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
              (33%nat, mkAF 8 5447 0); (12%nat, mkAF 1 7 0); (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
       [mkAC BC_GEU (SOff 33 0) (SOff 32 0)]
       [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0)]))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82da4) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
    - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
      rewrite (w10_den_sh _ 21 23 (pp + 0x4000) E21 ltac:(lia) E23). exact P20.
    - vm_compute. reflexivity.
    - constructor; [|constructor].
      apply (hm_ro_region rsegs _ (w_H W2) mem2 21 (pp + 0x4000)).
      + rewrite E21. rewrite unsigned_lit_small by lia. reflexivity.
      + lia. + lia.
      + constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (pp + 0x4000) 0 8 (SOff 32 0) Lp).
        * exact (w10_den_atom _ 32 Lp E32). * cbn. lia. * cbn. lia. * rewrite Z.add_0_r. exact HLv.
    - cbn. tauto.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
      refine (conj _ (conj (conj _ I) (conj _ I))).
      + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E21, E23, E32, E33, E12, E13, E14.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
        repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
        try (rewrite Z.pow_0_r; apply Z.mod_1_r).
        change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
      + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
        apply negb_true_iff, Z.ltb_ge. lia.
      + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia. }
  assert (SHOK : sh_ok rsegs W10Bx [mkSHE 21 0 8] E (mrestrict (w_H W2) mem2)).
  { constructor; [|constructor].
    apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia. }
  unfold cfg_at. change (w64 HS_R) with (Z_to_bv 64 0x82da4).
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82e2c.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
    destruct Hr as [<-|[]]. cbn in Hrb. lia. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2) [Z_to_bv 5 11; Z_to_bv 5 16; Z_to_bv 5 20] HS HAE
    ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000) E21 ltac:(lia) E23). symmetry. exact P20. }
  assert (Hcell : forall o i, 0 <= o < 0x160 -> 0 <= i < 8 ->
    aview rsegs (w_H W2) (ms_mem ms) (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
  { intros o i Ho Hi. apply HK. unfold T_SEG_STK, ASTACK in *. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
      apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
    + apply HPgSteps.same_io_wvb.
    + intros a Ha _. exact (HK a Ha).
    + intros a [].
  - apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HLpost).
    intros f Hf. unfold hs_L_post in Hf. cbv zeta in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv];
      first [ exact RK20
            | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
            | (intros i Hi; apply Hcell; lia) ] |]).
    destruct Hf.
  - apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) hs_P0 Hfsh).
    intros i Hi. apply HK. change (length hs_P0) with 80%nat in Hi.
    pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF. lia.
  - rewrite <- Hkbs. apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) pp _ Hpp).
    assert (X : Z.of_nat (length (hs_img_corr sh ps off bs kz)) = PP_SIZE) by exact (Himgl kk ltac:(lia)).
    intros y Hy. rewrite X in Hy. apply HK. unfold PP_SIZE in Hy. lia.
  - exact Hin.
  - exists j. split; [exact Hj | exact Hrj].
  - exact Hwf.
  - exact Hlen.
  - exact Htie.
  - exact Hoff.
  - unfold hs_plen. exact Hob.
  - exact Hb7. }
destruct r as [|x r1].
{ (* no input left: the byte is 0 *)
  cbv beta iota in E35, HE, HAE.
  assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
  assert (Hsk : skipn kk bs = Z_to_bv 8 0 :: fst (fuzz_u8s (length bs - S kk) [])).
  { rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply w10_fuzz_u8s_nil. }
  assert (Hsuf' : hs_suffix rest []) by (exists j; split; [exact Hj | exact Hrj]).
  assert (Hy0 : bv_unsigned (Z_to_bv 8 0 : byte) = 0) by reflexivity.
  change (Z.of_nat (length (@nil byte))) with 0 in E15.
assert (HS : st_ok rsegs E (mkSS 0x82da4
  (sr_set sr_atoms (Z_to_bv 5 20) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)))
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 9%nat) 0xf0 0xf8 0 0 [YP09.mkChunk 0xf0 (CVal 8 (SOff 36 0))]] None
  (mkFacts [(21%nat, mkAF 4096 W10_HI 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 W10_HI 0);
            (15%nat, mkAF 0 0 0); (12%nat, mkAF 1 7 0);
            (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
     [mkAC BC_LTU (SOff 33 0) (SOff 32 0); mkAC BC_EQ (SOff 15 0) (SLit 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 33 0) (SOff 36 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82da4) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000) E21 ltac:(lia) E23). exact P20.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (hm_rw_region rsegs _ (w_H W2) mem2 34 (pp + off + kz)).
      * rewrite E34. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * intros o Ho. apply Hpres. lia.
      * constructor.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 21 (pp + 0x4000)).
      * rewrite E21. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (pp + 0x4000) 0 8 (SOff 32 0) Lp).
        -- exact (w10_den_atom _ 32 Lp E32). -- cbn. lia. -- cbn. lia. -- rewrite Z.add_0_r. exact HLv.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e cx))).
      * rewrite E9. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor].
        apply (w10_ch8 _ _ _ _ _ pp); [exact (w10_den_atom _ 36 _ E36) | lia | exact Qf0].
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
    rewrite E34, E21, E9, !unsigned_lit_small by lia.
    pose proof (HRcell 0xf0 ltac:(lia) ltac:(lia)). unfold PP_SIZE in *.
    repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ (conj _ I)) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21, E23, E32, E33, E34, E15, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (w10_U_atom _ 15 0 E15 ltac:(lia)), U_lit by lia.
      reflexivity.
    + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (w10c_den_add _ 33 36 (off + kz) pp E33 ltac:(lia) E36 ltac:(lia)), (w10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the store target and the length word inside the first block, the input byte *)
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 34 0 1; mkSHE 21 0 8] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia. }
unfold cfg_at. change (w64 HS_R) with (Z_to_bv 64 0x82da4).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82e2c.
{ cbn [ss_mem].
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
  { rewrite E34. apply unsigned_lit_small. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok w10_tbl_ok HS SHOK W10Bspan.
- (* a2 - 1 <> 0: the next turn *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82da4.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.

  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
  { rewrite Hy0. pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (w7_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SLit 0) 0 HR0);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | reflexivity
      | cbn; lia | cbn; lia ]. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 16; Z_to_bv 5 17; Z_to_bv 5 20] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000));
      [symmetry; exact P20 | rewrite !ew_ewset_other by lia; exact E21 | exact Hpp47
      | rewrite !ew_ewset_other by lia; exact E23]. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 26; 20; 18] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK20 | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])] |]).
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
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (hs_cur rsegs cx rest [])).
  { rewrite RK; [exact P10 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length (@nil byte)))).
  { rewrite RK; [exact P15 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps [] off bs cnt).
  apply (w10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] [] (Z_to_bv 8 0)
    HP HRc HJ ltac:(eapply same_io_trans; apply HPgSteps.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82e2c.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.

  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
  { rewrite Hy0. pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (w7_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SLit 0) 0 HR0);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | reflexivity
      | cbn; lia | cbn; lia ]. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 16; Z_to_bv 5 17; Z_to_bv 5 20] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000));
      [symmetry; exact P20 | rewrite !ew_ewset_other by lia; exact E21 | exact Hpp47
      | rewrite !ew_ewset_other by lia; exact E23]. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 26; 20; 18] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK20 | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs []).
  exact (w10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] [] (Z_to_bv 8 0)
    HP HRc HJ ltac:(eapply same_io_trans; apply HPgSteps.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
}
cbv beta iota in E35, HE, HAE.
assert (Hjr : (j < length rest)%nat) by (cbn [length] in Hrl; lia).
assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
assert (Hsk : skipn kk bs = x :: fst (fuzz_u8s (length bs - S kk) r1)).
{ rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply w10_fuzz_u8s_cons. }
assert (Hsuf' : hs_suffix rest r1).
{ exists (S j). split; [lia | symmetry; exact (proj2 (w10c_skipn_cons rest j x r1 (eq_sym Hrj)))]. }
assert (Hx : val_mem rsegs (mrestrict (w_H W2) mem2) cur 1 (bv_unsigned x)).
{ destruct (garr8_nthZ rsegs _ _ _ (Z.of_nat j) Hbytes ltac:(lia) ltac:(unfold hd_zbytes; rewrite length_map; lia)) as [V _].
  rewrite Nat2Z.id, (w10c_nth_skipn rest j x r1 (eq_sym Hrj)) in V. rewrite Hcur. exact V. }
pose proof (bv_unsigned_in_range _ x) as Hxr. unfold bv_modulus in Hxr. change (Z.of_N 8) with 8 in Hxr.
assert (HS : st_ok rsegs E (mkSS 0x82da4
  (sr_set sr_atoms (Z_to_bv 5 20) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)))
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))];
   YP09.mkRegion (Some 9%nat) 0xf0 0xf8 0 0 [YP09.mkChunk 0xf0 (CVal 8 (SOff 36 0))]] None
  (mkFacts [(21%nat, mkAF 4096 W10_HI 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 W10_HI 0); (35%nat, mkAF 0 255 0);
            (10%nat, mkAF 1 (2 ^ 47 - 2) 0); (15%nat, mkAF 1 (2 ^ 47) 0); (12%nat, mkAF 1 7 0);
            (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)] [mkAC BC_LTU (SOff 33 0) (SOff 32 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 33 0) (SOff 36 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82da4) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000) E21 ltac:(lia) E23). exact P20.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (hm_rw_region rsegs _ (w_H W2) mem2 34 (pp + off + kz)).
      * rewrite E34. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * intros o Ho. apply Hpres. lia.
      * constructor.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 21 (pp + 0x4000)).
      * rewrite E21. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (pp + 0x4000) 0 8 (SOff 32 0) Lp).
        -- exact (w10_den_atom _ 32 Lp E32). -- cbn. lia. -- cbn. lia. -- rewrite Z.add_0_r. exact HLv.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 10 cur).
      * rewrite E10. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 35 0) (bv_unsigned x)).
        -- exact (w10_den_atom _ 35 _ E35). -- cbn. lia. -- cbn. lia. -- rewrite Z.add_0_r. exact Hx.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e cx))).
      * rewrite E9. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor].
        apply (w10_ch8 _ _ _ _ _ pp); [exact (w10_den_atom _ 36 _ E36) | lia | exact Qf0].
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
    rewrite E34, E21, E10, E9, !unsigned_lit_small by lia.
    destruct (Hindisj cur ltac:(lia)) as (_ & Hw1 & Hnp). unfold PP_SIZE in Hnp.
    assert (HnR : ~ (e_R (x_e cx) <= cur < e_R (x_e cx) + 0x160)).
    { intros X. apply Hw1. unfold hd_inw. cbn [hi_w1 headamp_himg_A].
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
    pose proof (HRcell 0xf0 ltac:(lia) ltac:(lia)). unfold PP_SIZE in *.
    repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ I) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21, E23, E32, E33, E34, E35, E10, E15, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (w10c_den_add _ 33 36 (off + kz) pp E33 ltac:(lia) E36 ltac:(lia)), (w10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the store target and the length word inside the first block, the input byte *)
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 34 0 1; mkSHE 21 0 8; mkSHE 10 0 1] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia.
  - apply (w10c_shent_in E _ 10 src (e_left (x_e cx)) cur Hamr HB (w10_U_atom E 10 _ E10 ltac:(lia))); [lia | lia | exact Hra]. }
unfold cfg_at. change (w64 HS_R) with (Z_to_bv 64 0x82da4).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82e2c.
{ cbn [ss_mem].
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
  { rewrite E34. apply unsigned_lit_small. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok w10_tbl_ok HS SHOK W10Bspan.
- (* a2 - 1 <> 0: the next turn *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82da4.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
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
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (w7_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SOff 35 0) (bv_unsigned x) HR0);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | apply (w10_den_atom _ 35); rewrite !ew_ewset_other by lia; exact E35
      | cbn; lia | cbn; lia ]. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15; Z_to_bv 5 16;
     Z_to_bv 5 17; Z_to_bv 5 20] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000));
      [symmetry; exact P20 | rewrite !ew_ewset_other by lia; exact E21 | exact Hpp47
      | rewrite !ew_ewset_other by lia; exact E23]. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 26; 20; 18] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK20 | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])] |]).
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
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (hs_cur rsegs cx rest r1)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 10) HS). w10_sr_eval.
    rewrite (w10_den_off _ 10 cur 1) by (rewrite !ew_ewset_other by lia; exact E10).
    f_equal. unfold cur, hs_cur. cbn [length]. lia. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length r1))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 15) HS). w10_sr_eval.
    rewrite (w10_den_off _ 15 (Z.of_nat (length (x :: r1))) (-1)) by (rewrite !ew_ewset_other by lia; exact E15).
    f_equal. cbn [length]. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r1 off bs cnt).
  apply (w10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply HPgSteps.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82e2c.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
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
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (w7_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SOff 35 0) (bv_unsigned x) HR0);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | apply (w10_den_atom _ 35); rewrite !ew_ewset_other by lia; exact E35
      | cbn; lia | cbn; lia ]. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15; Z_to_bv 5 16;
     Z_to_bv 5 17; Z_to_bv 5 20] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000));
      [symmetry; exact P20 | rewrite !ew_ewset_other by lia; exact E21 | exact Hpp47
      | rewrite !ew_ewset_other by lia; exact E23]. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 26; 20; 18] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK20 | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r1).
  exact (w10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply HPgSteps.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
Qed.
End c.
Print Assumptions w10_corr.
