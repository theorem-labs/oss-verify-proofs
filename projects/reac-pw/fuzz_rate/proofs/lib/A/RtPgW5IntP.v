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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 361 of its 394 lines of code are new or changed and 257 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSel.v at a529a88a6181 (the latch blocks
   pa_latch / pa_latch7) and the latch piece pa_piece_latch of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same
   commit, for reac-pw/fuzz_rate image A: rate's pcs and real-frame cells (i at R+0xf8, seen' at R+0xc8, np at
   R+0xd0); the latch's third entry 0x8252c (pa_latchi, from the Int-7 piece with i in a6) is new; the block post is
   lib/A/RtPgSteps.v rts_post; the cut lists are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropSel.v, with its module names changed; 219 of its 271 lines of code are new or changed and 342 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses from the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the piece lemma of the Int-7 value pod in
   LLVMFuzzerTestOneInput (0x80714), SELI 0x82280 -> LATCH' 0x8252c, as lib/A/RtPgSeg.v states it
   (rs_piece_W5_int_stmt). Proves no function (kind: segment lemma).

   HOW. The cut SELI gives the code's facts (registers, real-frame cells, pp->len from the first block's image); the
   core walk (lib/A/RtPgW5Int.v w5_int_core, which calls __asan_memset under the Section hypothesis W5_AMEMSET) runs
   from them to 0x8252c; the cut LATCH' is rebuilt from its post: the journal and frame part (RtPgW5Seg w5_core_post),
   the (location, value) facts (kept, and a6 = the property index, s8 = what is left of the input, s10 = -0x4001 from
   the core's post), the frame's shadow (kept), the first block's image (Model.pc_buf_prop with the Int pod of value 7
   after the key and flags words, and has_params := 1 when this is the first params property: RtPgW5Seg w5_img_gen)
   and the model facts (Model.prop_step's volume and Int-params arms). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgW5Kit RtPgW5Seg RtPgW5Int.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgPropLib.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image A's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* membership in a cut's (location, value) list, and a location of the end cut the piece kept: from the start cut's
   list Hat, its register outside w5i_clob (Hkeep) or its 8 bytes in a range the piece did not write (Kc) *)
Ltac w5i_in := cbn [rs_L_KEY rs_Rc rs_Rc0 rs_Kc rs_Hc rs_cur2 app In fst snd]; repeat (first [left; reflexivity | right]).
Ltac w5i_kept Hat Hkeep Kc := lazymatch goal with |- rt_at _ _ _ _ _ ?l ?v =>
  apply (rtm_at_kept rsegs _ _ _ _ _ _ _ l v (proj1 (Forall_forall _ _) Hat (l, v) ltac:(w5i_in)));
  cbn [rtm_keeps rt_xv];
  first [ apply Hkeep; [vm_compute; discriminate | apply w5i_notin; vm_compute; reflexivity]
        | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Kc; lia ] end.

(* ---- the model of one Int property (Model.prop_step's volume and Int-params arms) ---- *)
Lemma w5i_key_range : forall sel, 0 <= rs_key_of sel < 2 ^ 32.
Proof. intros sel. unfold rs_key_of. destruct (sel mod 4 =? 0); lia. Qed.
Lemma w5i_loop_int : forall sh ps sel r rest, sh <> 7 ->
ps = fst (props_loop sh (length ps) (rs_r0 rest)) ->
(sel, r) = fuzz_u8 (snd (props_loop sh (length ps) (rs_r0 rest))) ->
(sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
(ps ++ [(rs_key_of sel, PInt 7)], r) = props_loop sh (length (ps ++ [(rs_key_of sel, PInt 7)])) (rs_r0 rest).
Proof.
intros sh ps sel r rest Hsh Hps Hs Hb. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, props_loop_S_end.
remember (props_loop sh (length ps) (rs_r0 rest)) as pl eqn:EL. destruct pl as [ps0 r0].
cbn [fst snd] in Hps, Hs. subst ps0. cbv beta iota.
unfold prop_step. rewrite <- Hs. cbv beta iota.
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
unfold rs_key_of. destruct (Z.eqb_spec (sel mod 4) 0) as [E|E].
- reflexivity.
- destruct Hb as [Hb|Hb]; [lia|]. rewrite Hb. reflexivity.
Qed.
Lemma w5i_seen_int : forall ps sel,
rs_seen (ps ++ [(rs_key_of sel, PInt 7)]) = if sel mod 4 =? 0 then rs_seen ps else 1.
Proof.
intros ps sel. unfold rs_seen. rewrite existsb_app. cbn [existsb fst]. unfold rs_key_of, POD_PROP_PARAMS.
destruct (sel mod 4 =? 0); cbn [Z.eqb Pos.eqb orb]; [rewrite orb_false_r; reflexivity | rewrite orb_true_r; reflexivity].
Qed.
Lemma w5i_wf_int : forall sh ps k, rs_wf sh ps -> (length ps <= 2)%nat -> 0 <= k < 2 ^ 32 ->
rs_wf sh (ps ++ [(k, PInt 7)]).
Proof.
intros sh ps k (Hs & Hk & He & Hl) H2 Hk2. split; [exact Hs|]. split.
- apply Forall_app. split; [exact Hk|]. constructor; [cbn; split; [exact Hk2 | exact I] | constructor].
- split; [unfold all_ents in *; rewrite flat_map_app; cbn; rewrite app_nil_r; exact He|].
  rewrite length_app. cbn. lia.
Qed.
Lemma w5i_first_some : forall ps v, first_params ps = Some v -> rs_first ps = 0.
Proof.
intros ps v H. destruct (w5_first_range ps) as [E|E]; [exact E|].
rewrite (w5_first1 ps E) in H. discriminate H.
Qed.
Lemma w5i_first_none : forall ps, first_params ps = None -> rs_first ps = 1.
Proof.
intros ps H. destruct (Z.eq_dec (rs_first ps) 1) as [E|E]; [exact E|].
destruct (w5_first0 ps E) as [v Hv]. rewrite Hv in H. discriminate H.
Qed.
(* the image after the Int pod: the pod after the key and flags words, has_params set when the property is the first
   params one (the code's first cell R+0x110 is 1 exactly then) *)
Lemma w5i_img_int : forall sh ps sel, sh <> 7 ->
pc_image (PbCut sh (ps ++ [(rs_key_of sel, PInt 7)]) None) =
pp_image ((pc_buf (PbCut sh ps None) ++ le32 (rs_key_of sel) ++ le32 0) ++ enc_val (PInt 7))
  (is_props (PodRec sh ps None))
  (has_params (PodRec sh ps None) || ((if sel mod 4 =? 0 then 0 else rs_first ps) =? 1))
  (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
Proof.
intros sh ps sel Hsh. unfold pc_image. cbn [pc_shape pc_props pc_open].
rewrite <- pc_buf_prop. unfold prop_bytes. replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
cbn [fst snd]. rewrite <- !app_assoc.
unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open]. rewrite first_params_app.
destruct (first_params ps) as [v|] eqn:FP.
- rewrite (w5i_first_some ps v FP). destruct (sel mod 4 =? 0); cbn [Z.eqb Pos.eqb orb]; reflexivity.
- rewrite (w5i_first_none ps FP). unfold rs_key_of, POD_PROP_PARAMS.
  destruct (sel mod 4 =? 0); cbn [fst snd Z.eqb Pos.eqb orb]; reflexivity.
Qed.
Lemma w5i_pod_bytes : enc_val (PInt 7) = Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 7 ++ repeat (Z_to_bv 8 0) 4.
Proof. reflexivity. Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* __asan_memset (0x51cfc, neutral name checked_memset), lib/A/AE2r.v asan_memset_realizes *)
Hypothesis W5_AMEMSET : aintrin_realizes rsegs B OSet 0x51cfc.

Lemma w5_piece_int : rs_piece_W5_int_stmt rsegs B MT.
Proof using MTL LAWS W5_AMEMSET.
unfold rs_piece_W5_int_stmt. intros cx POST rest i Hst HL.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (w5_pre_facts B LAWS cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
pose proof Hpre as Hpre'. unfold rs_pre, rt_seg_pre in Hpre'. destruct Hpre' as (_ & Hnev & _ & G3 & G4 & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
unfold rs_from_SELI. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hqlen & Hpsl & Hsh & Hnp & Hps & Hnp3).
unfold rs_at_cx in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walk takes ---- *)
assert (A2 : getr regs2 2 = w64 (q_R (x_e cx))).
{ rewrite <- (w5_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w5_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
assert (A3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite <- (w5_getr5 regs2 3%bv 3 eq_refl). rewrite (Hr234 3 (or_intror (or_introl eq_refl))).
  rewrite (w5_getr5 (x_regs cx) 3%bv 3 eq_refl). exact G3. }
assert (A4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite <- (w5_getr5 regs2 4%bv 4 eq_refl). rewrite (Hr234 4 (or_intror (or_intror eq_refl))).
  rewrite (w5_getr5 (x_regs cx) 4%bv 4 eq_refl). exact G4. }
pose proof (w5_at_reg _ _ _ _ _ 9 (q_R (x_e cx)) Hat ltac:(w5i_in)) as A9.
pose proof (w5_at_reg _ _ _ _ _ 10 (rs_at_of sh ps - 0x3ffd) Hat ltac:(w5i_in)) as A10.
pose proof (w5_at_reg _ _ _ _ _ 22 (shadow_addr (q_pp (x_e cx) + 0x4000)) Hat ltac:(w5i_in)) as A22.
pose proof (w5_at_reg _ _ _ _ _ 23 (q_pp (x_e cx) + 0x4000) Hat ltac:(w5i_in)) as A23.
pose proof (w5_at_reg _ _ _ _ _ 18 SHADOW_OFF Hat ltac:(w5i_in)) as A18.
pose proof (w5_at_reg _ _ _ _ _ 24 (Z.of_nat (length r)) Hat ltac:(w5i_in)) as A24.
pose proof (w5_at_reg _ _ _ _ _ 26 (-0x4001) Hat ltac:(w5i_in)) as A26.
pose proof (w5_at_reg _ _ _ _ _ 27 (q_pp (x_e cx)) Hat ltac:(w5i_in)) as A27.
pose proof (w5_at_cell _ _ _ _ _ 0xe0 (rs_at_of sh ps) Hat ltac:(w5i_in)) as Va0.
pose proof (w5_at_cell _ _ _ _ _ 0x110 (if sel mod 4 =? 0 then 0 else rs_first ps) Hat ltac:(w5i_in)) as Vd0.
pose proof (w5_at_cell _ _ _ _ _ 0x88 (q_pp (x_e cx) + 0x400c) Hat ltac:(w5i_in)) as V50.
pose proof (w5_at_cell _ _ _ _ _ 0xf8 (Z.of_nat (length ps)) Hat ltac:(w5i_in)) as Vf8.
pose proof (w5_at_cell _ _ _ _ _ 0x118 (-0x4001) Hat ltac:(w5i_in)) as V118.
pose proof (w5_at_cell _ _ _ _ _ 0x130 (-0x3ffd) Hat ltac:(w5i_in)) as Ve8.
pose proof (w5_plen_lo sh ps Hsh7) as Hplen.
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [Hblen [cb Hcb]].
destruct (RtPgPropLib.pa_img_bounds sh ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
assert (HatE : rs_at_of sh ps = rs_plen sh ps + 8) by reflexivity.
assert (Hat16 : 16 <= rs_at_of sh ps) by lia.
assert (Hal : rs_at_of sh ps + 16 <= 5440) by (unfold rs_plen in HatE; lia).
assert (Hal8 : rs_at_of sh ps mod 8 = 0).
{ rewrite HatE. unfold rs_plen. rewrite Hcb. replace (cb * 8 + 8) with ((cb + 1) * 8) by lia. apply Z_mod_mult. }
assert (Hfst : (if sel mod 4 =? 0 then 0 else rs_first ps) = 0 \/ (if sel mod 4 =? 0 then 0 else rs_first ps) = 1).
{ destruct (sel mod 4 =? 0); [left; reflexivity | exact (w5_first_range ps)]. }
assert (Hidx : 0 <= Z.of_nat (length ps) <= 2) by lia.
assert (Hcur : 0 <= rs_cur rsegs cx rest r < 2 ^ 64).
{ destruct Hin as (Hl & _ & _ & _ & _ & Hs0 & Hs63 & _). destruct Hsuf as (j & Hj & ->).
  unfold rs_cur. rewrite length_skipn. lia. }
assert (Hnr : 0 <= Z.of_nat (length r) < 2 ^ 64).
{ destruct Hin as (Hl & _ & _ & _ & _ & Hs0 & Hs63 & _). destruct Hsuf as (j & Hj & ->).
  rewrite length_skipn. lia. }
rewrite Z.mod_small in Va0 by lia. rewrite Z.mod_small in Vd0 by (destruct Hfst as [-> | ->]; lia).
rewrite Z.mod_small in V50 by (unfold PP_SIZE in *; lia). rewrite Z.mod_small in Vf8 by lia.
(* pp->len at SELI: the key and flags words are written, so len = at *)
assert (Old : rtm_bytes rsegs (w_H W2) mem2 (q_pp (x_e cx)) (rs_img_key sh ps (rs_key_of sel))) by exact Hpp.
assert (Hblen8 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 (rs_key_of sel) ++ le32 0)) = rs_at_of sh ps).
{ rewrite !zlen_app, !zlen_le32. unfold rs_at_of, rs_plen. lia. }
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 (rs_at_of sh ps)).
{ rewrite <- Hblen8. unfold rs_img_key in Old.
  refine (rtm_pp_len rsegs _ _ _ _ _ _ _ IB3 IB4 _ _ _ Old). rewrite Hblen8. unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (q_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
(* ---- the core walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs RS_SELI regs2 mem2 md2) with (cfg_at rsegs 0x82280 regs2 mem2 md2).
  exact (w5_int_core B MT MTL LAWS W5_AMEMSET (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (q_R (x_e cx)) (q_pp (x_e cx)) (rs_at_of sh ps)
    (if sel mod 4 =? 0 then 0 else rs_first ps) (Z.of_nat (length ps)) (Z.of_nat (length r))
    HJ Ppin2 Ppout Hnev A2 A9 A3 A4 A10 A22 A23 A18 A24 A26 A27 Va0 Vd0 V50 Vf8 V118 Ve8 Vlen RB3 RB1 RB2
    Hat16 Hal Hal8 Hfst Hidx Hnr). }
intros W3 c3 Hle Hpost.
set (fsv := if sel mod 4 =? 0 then 0 else rs_first ps) in *.
assert (HEp : forall a, (q_pp (x_e cx) + rs_at_of sh ps <= a < q_pp (x_e cx) + rs_at_of sh ps + 16) \/
  (q_pp (x_e cx) + 0x4000 <= a < q_pp (x_e cx) + 0x4008) \/
  (fsv = 1 /\ q_pp (x_e cx) + 0x400c <= a < q_pp (x_e cx) + 0x4010) -> rs_E1 rsegs cx a).
{ intros a [Ha|[Ha|[_ Ha]]]; right; unfold PP_SIZE; lia. }
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) -> ~ In (Z_to_bv 5 r0) w5i_clob).
{ intros r0 [-> | [-> | ->]]; apply w5i_notin; vm_compute; reflexivity. }
destruct (w5_core_post B MT MTL cx (rs_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x8252c w5i_clob _ W3 c3
  Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rpod & Rlen & Rfl & G16 & G24 & G26)).
assert (Hsp : spZ regs2 = q_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* every byte the piece did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) ->
  ~ (q_pp (x_e cx) + rs_at_of sh ps <= a < q_pp (x_e cx) + rs_at_of sh ps + 16) ->
  ~ (q_pp (x_e cx) + 0x4000 <= a < q_pp (x_e cx) + 0x4008) ->
  ~ (fsv = 1 /\ q_pp (x_e cx) + 0x400c <= a < q_pp (x_e cx) + 0x4010) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3 H4. apply Hmem; [exact Ha | rewrite Hsp; exact H1 |]. intros [X|[X|X]]; auto. }
assert (Kc : forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x140 ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
(* ---- the cut LATCH' ---- *)
change (cfg_at rsegs 0x8252c regs3 mem3 md3) with (cfg_at rsegs RS_LATCHI regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 sh np (ps ++ [(rs_key_of sel, PInt 7)]) r);
  [rewrite length_app, Hlen; cbn [length]; lia|].
split.
- split; [exact Hcore3|].
  split.
  { unfold rs_fsh_at in *. eapply rtm_fsh_kept; [exact Hfsh|]. intros j Hj.
    change (length rs_P0) with 56%nat in Hj.
    pose proof (Z.mul_div_le (q_F (x_e cx)) 8 ltac:(lia)) as D1.
    pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia) ltac:(lia)) as D2.
    unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg in PApp.
    apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
  split.
  { unfold rs_pp_at.
    change (rtm_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx)) (pc_image (PbCut sh (ps ++ [(rs_key_of sel, PInt 7)]) None))).
    rewrite (w5i_img_int sh ps sel Hsh7). fold fsv.
    set (b := pc_buf (PbCut sh ps None) ++ le32 (rs_key_of sel) ++ le32 0) in *.
    assert (LP : length (enc_val (PInt 7)) = 16%nat) by reflexivity.
    assert (Hbl : Z.of_nat (length b) = rs_at_of sh ps) by exact Hblen8.
    unfold rs_img_key in Old. fold b in Old.
    assert (Nb : rtm_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx)) (b ++ enc_val (PInt 7))).
    { apply rtm_bytes_app. split.
      - eapply rtm_bytes_kept; [exact (w5_img_buf _ _ _ _ _ _ _ _ _ Old)|]. intros y Hy.
        apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia.
      - rewrite Hbl, w5i_pod_bytes. exact Rpod. }
    apply (w5_img_gen (w_H W2) mem2 (w_H W3) mem3 (q_pp (x_e cx)) b _ _
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
    - rewrite length_app. lia.
    - rewrite length_app, LP, Nat2Z.inj_add, Hbl. change (Z.of_nat 16) with 16. unfold POD_BUF_MAX. lia.
    - exact IB3.
    - exact IB4.
    - rewrite length_app, LP, Nat2Z.inj_add, Hbl. change (Z.of_nat 16) with 16. unfold OFF_LEN. exact Rlen.
    - destruct (Z.eqb_spec fsv 1) as [E|E].
      + rewrite orb_true_r. exact (Rfl E).
      + rewrite orb_false_r. refine (proj1 (w5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ IB3 IB4 Old _));
          [rewrite Hbl; unfold POD_BUF_MAX; lia|].
        intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia;
        intros [X _]; exact (E X).
    - assert (HbB : Z.of_nat (length b) <= POD_BUF_MAX) by (rewrite Hbl; unfold POD_BUF_MAX; lia).
      eapply rtm_bytes_kept;
        [apply rtm_bytes_of_val; exact (rtm_pp_params_struct rsegs _ _ _ _ _ _ HbB IB3 IB4 _ _ _ Old)|].
      intros y Hy. rewrite ?length_le32, ?length_Z_to_le_bytes in Hy. unfold OFF_PARAMS_STRUCT in Hy.
      apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia.
    - intros y Hy. rewrite length_app, LP, Nat2Z.inj_add, Hbl in Hy. change (Z.of_nat 16) with 16 in Hy.
      unfold OFF_LEN, OFF_IS_PROPS, OFF_HAS_PARAMS, OFF_ENT, PP_SIZE in Hy.
      apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
  split; [exact Hin|]. split; [exact Hsuf|].
  split; [apply w5i_wf_int; [exact Hwf | lia | exact (w5i_key_range sel)]|].
  split; [exact Hsh|]. split; [exact Hnp|].
  split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hnp3|].
  exact (w5i_loop_int sh ps sel r rest Hsh7 Hpsl Hselr Hsel4).
- unfold rs_at_cx, rs_at, rs_L_LATCH.
  rewrite (w5i_seen_int ps sel).
  replace (Z.of_nat (length (ps ++ [(rs_key_of sel, PInt 7)])) - 1) with (Z.of_nat (length ps))
    by (rewrite length_app; cbn [length]; lia).
  cbn [rs_Rc rs_Rc0 rs_Kc rs_Hc rs_cur2 app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: first
    [ w5i_kept Hat Hkeep Kc
    | (cbn [rt_at]; rewrite (w5_getr5 regs3 26%bv 26 eq_refl); exact G26)
    | (cbn [rt_at]; rewrite (w5_getr5 regs3 24%bv 24 eq_refl); exact G24)
    | (cbn [rt_at]; rewrite (w5_getr5 regs3 16%bv 16 eq_refl); exact G16) ].
Qed.
End p.

Print Assumptions w5_piece_int.
