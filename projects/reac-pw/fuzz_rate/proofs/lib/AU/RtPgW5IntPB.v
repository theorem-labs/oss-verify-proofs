(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v at 533bf30ff015 for image B (fuzz_rate.asan-ubsan): image B's block SEL7 0x80ff4 -> LATCH7 0x8257c (e into scope, memset(e.body, 0, 96) through lib/AU/RtPgStepsB.v rtsb_intrin_at at 0x51d54, e.size = e.type = 4, the call pod_write_ent(pp, e) 0x81054 through rtsb_pwe_at with lib/AU/PweSpec.v's contract at 0x83cc4 as a Section hypothesis, e out of scope) in three engine runs over the kit lib/AU/RtPgPropBKit.v, with the frame shadow, frame-object and record facts of lib/AU/RtPgMemB.v; the piece is lib/AU/RtPgSegB.v's rsb_piece_W4_int7_stmt with image B's cut lists. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgPropBInt7.v, with its module names changed; 250 of its 313 lines of code are new or changed and 676 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5IntP.v at a66696a9b1d1 for the same
   unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the cut vocabulary is lib/AU/RtPgSegB.v's
   (rsb_, SELI 0x82398 -> LATCH7 0x8257c, no LATCHI), the bridge lib/AU/RtPgW5SegB.v's (w5b_) and the memory layer
   lib/AU/RtPgMemB.v's (rtmb_); the core is lib/AU/RtPgW5IntB.v's w5b_int_core, which calls checked_memset and
   pod_write_ent under the Section hypotheses W5B_AMEMSET and W5B_PWE, so the piece carries two call hypotheses
   where image A carried one; the end cut's list carries s8 = -8 and a3 = seen (image A's a6 / s8 / s10 of the
   capacity bound are gone, image B reloading neither the property index nor the bound); the prefixes w5_ / w5i_
   become w5b_ / w5bp_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the piece lemma of the Int-7 value pod in
   LLVMFuzzerTestOneInput (0x8076c), SELI 0x82398 -> LATCH7 0x8257c, as lib/AU/RtPgSegB.v states it
   (rsb_piece_W5_int_stmt). Proves no function (kind: segment lemma).

   HOW. The cut SELI gives the code's facts (registers, real-frame cells, the first block's image with the key and
   flags words already written, so pp->len is `at`); the core walk (lib/AU/RtPgW5IntB.v w5b_int_core) runs from them
   to 0x8257c; the cut LATCH7 is rebuilt from its post: the journal and frame part (RtPgW5SegB w5b_core_post), the
   (location, value) facts (kept, and t0 = the property index, t4 = what is left, a3 = seen', s8 = -8 from the core's
   post), the frame's shadow back at the prologue's pattern (the core's post: e42's 13 granules are 0xf8 again), the
   first block's image (Model.pc_buf_prop with the Int pod of value 7 after the key and flags words, and has_params
   set when this is the first params property: RtPgW5SegB w5b_img_gen) and the model facts (Model.prop_step's volume
   and Int-params arms). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import PweSpec RtPgImgB RtPgMemB RtPgStepsB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW5KitB RtPgW5SegB RtPgW5IntB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.
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

(* ---- the model of one Int property (Model.prop_step's volume and Int-params arms) ---- *)
Lemma w5bp_key_range : forall sel, 0 <= rsb_key_of sel < 2 ^ 32.
Proof. intros sel. unfold rsb_key_of. destruct (sel mod 4 =? 0); lia. Qed.
Lemma w5bp_loop_int : forall sh ps sel r rest, sh <> 7 ->
ps = fst (props_loop sh (length ps) (rsb_r0 rest)) ->
(sel, r) = fuzz_u8 (snd (props_loop sh (length ps) (rsb_r0 rest))) ->
(sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
(ps ++ [(rsb_key_of sel, PInt 7)], r) = props_loop sh (length (ps ++ [(rsb_key_of sel, PInt 7)])) (rsb_r0 rest).
Proof.
intros sh ps sel r rest Hsh Hps Hs Hb. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, props_loop_S_end.
remember (props_loop sh (length ps) (rsb_r0 rest)) as pl eqn:EL. destruct pl as [ps0 r0].
cbn [fst snd] in Hps, Hs. subst ps0. cbv beta iota.
unfold prop_step. rewrite <- Hs. cbv beta iota.
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
unfold rsb_key_of. destruct (Z.eqb_spec (sel mod 4) 0) as [E|E].
- reflexivity.
- destruct Hb as [Hb|Hb]; [lia|]. rewrite Hb. reflexivity.
Qed.
Lemma w5bp_seen_int : forall ps sel,
rsb_seen (ps ++ [(rsb_key_of sel, PInt 7)]) = if sel mod 4 =? 0 then rsb_seen ps else 1.
Proof.
intros ps sel. unfold rsb_seen. rewrite existsb_app. cbn [existsb fst]. unfold rsb_key_of, POD_PROP_PARAMS.
destruct (sel mod 4 =? 0); cbn [Z.eqb Pos.eqb orb]; [rewrite orb_false_r; reflexivity | rewrite orb_true_r; reflexivity].
Qed.
Lemma w5bp_wf_int : forall sh ps k, rsb_wf sh ps -> (length ps <= 2)%nat -> 0 <= k < 2 ^ 32 ->
rsb_wf sh (ps ++ [(k, PInt 7)]).
Proof.
intros sh ps k (Hs & Hk & He & Hl) H2 Hk2. split; [exact Hs|]. split.
- apply Forall_app. split; [exact Hk|]. constructor; [cbn; split; [exact Hk2 | exact I] | constructor].
- split; [unfold all_ents in *; rewrite flat_map_app; cbn; rewrite app_nil_r; exact He|].
  rewrite length_app. cbn. lia.
Qed.
Lemma w5bp_first_some : forall ps v, first_params ps = Some v -> rsb_first ps = 0.
Proof.
intros ps v H. destruct (w5b_first_range ps) as [E|E]; [exact E|].
rewrite (w5b_first1 ps E) in H. discriminate H.
Qed.
Lemma w5bp_first_none : forall ps, first_params ps = None -> rsb_first ps = 1.
Proof.
intros ps H. destruct (Z.eq_dec (rsb_first ps) 1) as [E|E]; [exact E|].
destruct (w5b_first0 ps E) as [v Hv]. rewrite Hv in H. discriminate H.
Qed.
(* the image after the Int pod: the pod after the key and flags words, has_params set when the property is the
   first params one (the code's first cell R+0x160 is 1 exactly then) *)
Lemma w5bp_img_int : forall sh ps sel, sh <> 7 ->
pc_image (PbCut sh (ps ++ [(rsb_key_of sel, PInt 7)]) None) =
pp_image ((pc_buf (PbCut sh ps None) ++ le32 (rsb_key_of sel) ++ le32 0) ++ enc_val (PInt 7))
  (is_props (PodRec sh ps None))
  (has_params (PodRec sh ps None) || ((if sel mod 4 =? 0 then 0 else rsb_first ps) =? 1))
  (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
Proof.
intros sh ps sel Hsh. unfold pc_image. cbn [pc_shape pc_props pc_open].
rewrite <- pc_buf_prop. unfold prop_bytes. replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
cbn [fst snd]. rewrite <- !app_assoc.
unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open]. rewrite first_params_app.
destruct (first_params ps) as [v|] eqn:FP.
- rewrite (w5bp_first_some ps v FP). destruct (sel mod 4 =? 0); cbn [Z.eqb Pos.eqb orb]; reflexivity.
- rewrite (w5bp_first_none ps FP). unfold rsb_key_of, POD_PROP_PARAMS.
  destruct (sel mod 4 =? 0); cbn [fst snd Z.eqb Pos.eqb orb]; reflexivity.
Qed.
Lemma w5bp_pod_bytes : enc_val (PInt 7) = Model.enc_pod w5b_e42.
Proof. reflexivity. Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* checked_memset (0x51d54), the A3 lane's contract of the intrinsic *)
Hypothesis W5B_AMEMSET : aintrin_realizes rsegs B OSet 0x51d54.
(* pod_write_ent (0x83cc4), lib/AU/PweSpec.v's contract *)
Hypothesis W5B_PWE : pod_write_ent_specX rsegs B MT PWE_ENT.

Lemma w5b_piece_int : rsb_piece_W5_int_stmt rsegs B MT.
Proof using MTL LAWS W5B_AMEMSET W5B_PWE.
unfold rsb_piece_W5_int_stmt. intros cx POST rest i Hst HL.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hqlen0 & Hin0).
pose proof (w5b_pre_facts B LAWS cx Hpre)
  as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
pose proof Hpre as Hpre'. unfold rsb_pre, rt_seg_pre in Hpre'.
destruct Hpre' as (HJ0 & Hnev & _ & G3 & G4 & _ & _ & _ & _ & Hown & HFeq & _).
pose proof HJ0 as (_ & Hly0 & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
assert (HOL : Layout.OFF_LEN = 16384) by reflexivity.
assert (HPB : Layout.POD_BUF_MAX = 16384) by reflexivity.
unfold rsb_from_SELI. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hqlen & Hpsl & Hsh & Hnp & Hps & Hnp3).
unfold rsb_at_cx in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walk takes ---- *)
assert (A2 : getr regs2 2 = w64 (q_R (x_e cx))).
{ rewrite <- (w5b_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w5b_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
assert (A3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite <- (w5b_getr5 regs2 3%bv 3 eq_refl). rewrite (Hr234 3 (or_intror (or_introl eq_refl))).
  rewrite (w5b_getr5 (x_regs cx) 3%bv 3 eq_refl). exact G3. }
assert (A4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite <- (w5b_getr5 regs2 4%bv 4 eq_refl). rewrite (Hr234 4 (or_intror (or_intror eq_refl))).
  rewrite (w5b_getr5 (x_regs cx) 4%bv 4 eq_refl). exact G4. }
pose proof (w5b_at_reg _ _ _ _ _ 9 (q_R (x_e cx)) Hat ltac:(w5b_in)) as A9.
pose proof (w5b_at_reg _ _ _ _ _ 19 (shadow_addr (q_F (x_e cx))) Hat ltac:(w5b_in)) as A19.
pose proof (w5b_at_reg _ _ _ _ _ 20 SHADOW_OFF Hat ltac:(w5b_in)) as A20.
pose proof (w5b_at_reg _ _ _ _ _ 5 (Z.of_nat (length ps)) Hat ltac:(w5b_in)) as A5.
pose proof (w5b_at_reg _ _ _ _ _ 29 (Z.of_nat (length r)) Hat ltac:(w5b_in)) as A29.
pose proof (w5b_at_reg _ _ _ _ _ 14 (if sel mod 4 =? 0 then rsb_seen ps else 1) Hat ltac:(w5b_in)) as A14.
pose proof (w5b_at_reg _ _ _ _ _ 25 1 Hat ltac:(w5b_in)) as A25.
pose proof (w5b_at_cell _ _ _ _ _ 0x78 (q_F (x_e cx) + 0x18c) Hat ltac:(w5b_in)) as V78.
pose proof (w5b_at_cell _ _ _ _ _ 0x80 (q_F (x_e cx) + 0x180) Hat ltac:(w5b_in)) as V80.
pose proof (w5b_at_cell _ _ _ _ _ 0x90 (q_pp (x_e cx) + 0x400c) Hat ltac:(w5b_in)) as V90.
pose proof (w5b_at_cell _ _ _ _ _ 0x160 (if sel mod 4 =? 0 then 0 else rsb_first ps) Hat ltac:(w5b_in)) as V160.
pose proof (w5b_at_cell _ _ _ _ _ 0x168 (q_pp (x_e cx)) Hat ltac:(w5b_in)) as V168.
pose proof (w5b_plen_lo sh ps Hsh7) as Hplen.
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [Hblen [cb Hcb]].
destruct (w5b_img_bounds sh ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
assert (HatE : rsb_at_of sh ps = rsb_plen sh ps + 8) by reflexivity.
assert (Hat16 : 16 <= rsb_at_of sh ps) by lia.
assert (Hal : rsb_at_of sh ps + 16 <= 5440) by (unfold rsb_plen in HatE; lia).
assert (Hal8 : rsb_at_of sh ps mod 8 = 0).
{ rewrite HatE. unfold rsb_plen. rewrite Hcb. replace (cb * 8 + 8) with ((cb + 1) * 8) by lia. apply Z_mod_mult. }
assert (Hfst : (if sel mod 4 =? 0 then 0 else rsb_first ps) = 0 \/ (if sel mod 4 =? 0 then 0 else rsb_first ps) = 1).
{ destruct (sel mod 4 =? 0); [left; reflexivity | exact (w5b_first_range ps)]. }
assert (Hnr : 0 <= Z.of_nat (length r) < 2 ^ 64).
{ destruct Hin as (Hl & _ & _ & _ & _ & Hs0 & Hs63 & _). destruct Hsuf as (j & Hj & ->).
  rewrite length_skipn. lia. }
assert (Hsn : 0 <= (if sel mod 4 =? 0 then rsb_seen ps else 1) < 2 ^ 64).
{ destruct (sel mod 4 =? 0); [unfold rsb_seen; destruct (existsb _ _); cbn; lia | lia]. }
rewrite Z.mod_small in V78 by lia. rewrite Z.mod_small in V80 by lia.
rewrite Z.mod_small in V90 by (unfold Layout.PP_SIZE in *; lia).
rewrite Z.mod_small in V160 by (destruct Hfst as [-> | ->]; lia).
rewrite Z.mod_small in V168 by (unfold Layout.PP_SIZE in *; lia).
(* pp->len at SELI: the key and flags words are written, so len = at *)
assert (Old : rtmb_bytes rsegs (w_H W2) mem2 (q_pp (x_e cx)) (rsb_img_key sh ps (rsb_key_of sel))) by exact Hpp.
assert (Hblen8 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 (rsb_key_of sel) ++ le32 0)) = rsb_at_of sh ps).
{ rewrite !zlen_app, !zlen_le32. unfold rsb_at_of, rsb_plen. lia. }
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + Layout.OFF_LEN) 8 (rsb_at_of sh ps)).
{ rewrite <- Hblen8. unfold rsb_img_key in Old.
  refine (rtmb_pp_len rsegs _ _ _ _ _ _ _ IB3 IB4 _ _ _ Old). rewrite Hblen8. unfold Layout.POD_BUF_MAX; lia. }
assert (Ppin2 : In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
assert (HFA : q_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
{ pose proof HJ as (_ & Hly2 & _).
  rewrite (w5bi_fa _ (x_ly cx) ly2 4 (x_pos cx) Hly2).
  rewrite <- (w5bi_fa _ (x_ly cx) (x_lyc cx) 4 (x_pos cx) Hly0). exact HFeq. }
assert (Hctx : w5bi_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
  (x_md0 cx) (x_own cx) (x_k cx) ly2 S2 W2 mem2 md2 (q_R (x_e cx)) (q_F (x_e cx)) (x_pos cx)).
{ split; [exact HJ|]. split; [exact RB3|]. split; [exact RB2|]. split; [exact RB1|].
  split; [exact Hown | exact HFA]. }
(* ---- the frame, the block and their separation, as the core and the end cut need them ---- *)
destruct (w5bi_frame B LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
  (x_md0 cx) (x_own cx) (x_k cx) ly2 S2 W2 mem2 md2 (q_R (x_e cx)) (q_F (x_e cx)) (x_pos cx) Hctx)
  as (Hal32 & Happ & HF0 & HFc & Hsa0 & Hsac & Hsep & _ & _ & Hin4 & Hrlo & Hr47 & _).
destruct (w5bi_blk B LAWS ly2 S2 W2 mem2 md2 (q_pp (x_e cx)) (proj1 HJ) Ppin2)
  as (Hpp0 & Hpp16 & Hpp8 & Hppc & Hppapp & _).
assert (Hbf : q_pp (x_e cx) + 19744 <= q_F (x_e cx) \/ q_F (x_e cx) + 1024 <= q_pp (x_e cx)).
{ pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 (q_pp (x_e cx)) Layout.PP_SIZE 4 (x_pos cx)
    (proj1 HJ) Ppin2 Hin4) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz.
  change (req_size Layout.PP_SIZE) with 19744 in Hz. change (fs_frame_bytes 4) with 1024 in Hz.
  rewrite <- HFA in Hz. lia. }
assert (Hbs : forall j, 0 <= j < 128 -> ~ (q_pp (x_e cx) <= shadow_addr (q_F (x_e cx)) + j < q_pp (x_e cx) + 19744)).
{ intros j Hj. exact (w5bi_sep_sh_blk (q_F (x_e cx)) (q_pp (x_e cx)) j Hal32 HF0 HFc Hppapp Hj). }
(* ---- the core walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs RSB_SELI regs2 mem2 md2) with (cfg_at rsegs 0x82398 regs2 mem2 md2).
  exact (w5b_int_core B MT MTL LAWS W5B_AMEMSET W5B_PWE (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx)
    (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx) ly2 S2 W2 mem2 md2 regs2
    (q_R (x_e cx)) (q_F (x_e cx)) (q_pp (x_e cx)) (x_pos cx) (rsb_at_of sh ps)
    (if sel mod 4 =? 0 then 0 else rsb_first ps) (if sel mod 4 =? 0 then rsb_seen ps else 1)
    (Z.of_nat (length ps)) (Z.of_nat (length r))
    Hctx Ppin2 Ppout Hnev A2 A3 A4 A9 A19 A20 A5 A29 A14 A25 V78 V80 V90 V160 V168 Vlen Hfsh
    ltac:(lia) Hal8 ltac:(rewrite HPB; lia) Hfst ltac:(lia) Hnr Hsn). }
intros W3 c3 Hle Hpost.
set (fsv := if sel mod 4 =? 0 then 0 else rsb_first ps) in *.
assert (HEp : forall a, w5bi_E (q_F (x_e cx)) (q_pp (x_e cx)) (rsb_at_of sh ps) fsv a -> rsb_E1 rsegs cx a).
{ intros a [Ha | [Ha | [Ha | [_ Ha]]]].
  - apply w5b_E1_F. lia.
  - apply w5b_E1_fsh. lia.
  - apply w5b_E1_pp. unfold pwe_E in Ha. rewrite w5b_e42_len, HOL in Ha. unfold Layout.PP_SIZE. lia.
  - apply w5b_E1_pp. unfold Layout.PP_SIZE. lia. }
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) -> ~ In (Z_to_bv 5 r0) w5bi_clob).
{ intros r0 [-> | [-> | ->]]; apply w5bi_notin; vm_compute; reflexivity. }
destruct (w5b_core_post B MT MTL cx (rsb_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x8257c w5bi_clob _ W3 c3
  Hcore HEp Hclob Hpost)
  as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (GPOD & GLEN & GHP & GFSH & G5 & G29 & G13 & G24)).
assert (Hsp : spZ regs2 = q_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* every byte the piece did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) ->
  ~ w5bi_E (q_F (x_e cx)) (q_pp (x_e cx)) (rsb_at_of sh ps) fsv a ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2'. apply Hmem; [exact Ha | rewrite Hsp; exact H1 | exact H2']. }
assert (Kc : forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x180 ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Kp; [lia | rewrite HTS; lia |].
  unfold w5bi_E, pwe_E. rewrite w5b_e42_len, HOL. intros [Hy | [Hy | [Hy | [_ Hy]]]]; lia. }
(* a byte of the first block the piece did not write *)
assert (Kb : forall a, q_pp (x_e cx) <= a < q_pp (x_e cx) + 19744 ->
  ~ (q_pp (x_e cx) + rsb_at_of sh ps <= a < q_pp (x_e cx) + rsb_at_of sh ps + 16) ->
  ~ (q_pp (x_e cx) + 16384 <= a < q_pp (x_e cx) + 16392) ->
  ~ (fsv = 1 /\ q_pp (x_e cx) + 16396 <= a < q_pp (x_e cx) + 16400) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha N1 N2 N3. apply Kp; [lia | rewrite HTS; lia |].
  unfold w5bi_E, pwe_E. rewrite w5b_e42_len, HOL.
  intros [Hy | [Hy | [Hy | Hy]]]; [lia | | lia | exact (N3 Hy)].
  pose proof (Hbs (a - shadow_addr (q_F (x_e cx))) ltac:(lia)). lia. }
(* ---- the cut LATCH7 ---- *)
change (cfg_at rsegs 0x8257c regs3 mem3 md3) with (cfg_at rsegs RSB_LATCH7 regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 sh np (ps ++ [(rsb_key_of sel, PInt 7)]) r);
  [rewrite length_app, Hlen; cbn [length]; lia|].
split.
- split; [exact Hcore3|].
  split; [exact GFSH|].
  split.
  { unfold rsb_pp_at.
    change (rtmb_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx))
              (pc_image (PbCut sh (ps ++ [(rsb_key_of sel, PInt 7)]) None))).
    rewrite (w5bp_img_int sh ps sel Hsh7). fold fsv.
    set (b := pc_buf (PbCut sh ps None) ++ le32 (rsb_key_of sel) ++ le32 0) in *.
    assert (LP : length (enc_val (PInt 7)) = 16%nat) by reflexivity.
    assert (Hbl : Z.of_nat (length b) = rsb_at_of sh ps) by exact Hblen8.
    unfold rsb_img_key in Old. fold b in Old.
    assert (Nb : rtmb_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx)) (b ++ enc_val (PInt 7))).
    { apply rtmb_bytes_app. split.
      - eapply (rtmb_bytes_kept rsegs); [exact (w5b_img_buf _ _ _ _ _ _ _ _ _ Old)|].
        intros y Hy. rewrite Hbl in Hy. apply Kb; [lia | lia | lia | intros [_ X]; lia].
      - rewrite Hbl, w5bp_pod_bytes. exact GPOD. }
    apply (w5b_img_gen (w_H W2) mem2 (w_H W3) mem3 (q_pp (x_e cx)) b _ _
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
    - rewrite length_app. lia.
    - rewrite length_app, LP, Nat2Z.inj_add, Hbl. change (Z.of_nat 16) with 16.
      unfold Layout.POD_BUF_MAX. lia.
    - exact IB3.
    - exact IB4.
    - rewrite length_app, LP, Nat2Z.inj_add, Hbl. change (Z.of_nat 16) with 16.
      rewrite HOL. exact GLEN.
    - destruct (Z.eqb_spec fsv 1) as [E|E].
      + rewrite orb_true_r. unfold Layout.OFF_HAS_PARAMS. exact (GHP E).
      + rewrite orb_false_r.
        refine (proj1 (w5b_img_flags _ _ _ _ _ _ _ _ _ _ _ _ IB3 IB4 Old _));
          [rewrite Hbl; unfold Layout.POD_BUF_MAX; lia|].
        intros y Hy. unfold Layout.OFF_HAS_PARAMS, Layout.OFF_ENT in Hy.
        apply Kb; [lia | lia | lia | intros [X _]; exact (E X)].
    - assert (HbB : Z.of_nat (length b) <= Layout.POD_BUF_MAX)
        by (rewrite Hbl; unfold Layout.POD_BUF_MAX; lia).
      eapply (rtmb_bytes_kept rsegs);
        [apply rtmb_bytes_of_val; exact (rtmb_pp_params_struct rsegs _ _ _ _ _ _ HbB IB3 IB4 _ _ _ Old)|].
      intros y Hy. rewrite ?length_le32, ?length_Z_to_le_bytes in Hy.
      unfold Layout.OFF_PARAMS_STRUCT in Hy. apply Kb; [lia | lia | lia | intros [_ X]; lia].
    - intros y Hy. rewrite length_app, LP, Nat2Z.inj_add, Hbl in Hy. change (Z.of_nat 16) with 16 in Hy.
      unfold Layout.OFF_LEN, Layout.OFF_IS_PROPS, Layout.OFF_HAS_PARAMS, Layout.OFF_ENT,
        Layout.PP_SIZE in Hy.
      apply Kb; [lia | lia | lia | intros [_ X]; lia]. }
  split; [exact Hin|]. split; [exact Hsuf|].
  split; [apply w5bp_wf_int; [exact Hwf | lia | exact (w5bp_key_range sel)]|].
  split; [exact Hsh|]. split; [exact Hnp|].
  split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hnp3|].
  exact (w5bp_loop_int sh ps sel r rest Hsh7 Hpsl Hselr Hsel4).
- unfold rsb_at_cx, rsb_at, rsb_L_LATCH.
  rewrite (w5bp_seen_int ps sel).
  replace (Z.of_nat (length (ps ++ [(rsb_key_of sel, PInt 7)])) - 1) with (Z.of_nat (length ps))
    by (rewrite length_app; cbn [length]; lia).
  cbn [rsb_Rc rsb_Rc0 rsb_Kc rsb_Hc rsb_cur2 rsb_cur2s app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: first
    [ w5b_kept Hat Hkeep Kc
    | (cbn [rt_at]; rewrite (w5b_getr5 regs3 24%bv 24 eq_refl); exact G24)
    | (cbn [rt_at]; rewrite (w5b_getr5 regs3 5%bv 5 eq_refl); exact G5)
    | (cbn [rt_at]; rewrite (w5b_getr5 regs3 29%bv 29 eq_refl); exact G29)
    | (cbn [rt_at]; rewrite (w5b_getr5 regs3 13%bv 13 eq_refl); exact G13) ].
Qed.
End p.

Print Assumptions w5b_piece_int.
