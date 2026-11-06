(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v at 533bf30ff015 for image B (fuzz_rate.asan-ubsan): image B's block SEL7 0x80ff4 -> LATCH7 0x8257c (e into scope, memset(e.body, 0, 96) through lib/AU/RtPgStepsB.v rtsb_intrin_at at 0x51d54, e.size = e.type = 4, the call pod_write_ent(pp, e) 0x81054 through rtsb_pwe_at with lib/AU/PweSpec.v's contract at 0x83cc4 as a Section hypothesis, e out of scope) in three engine runs over the kit lib/AU/RtPgPropBKit.v, with the frame shadow, frame-object and record facts of lib/AU/RtPgMemB.v; the piece is lib/AU/RtPgSegB.v's rsb_piece_W4_int7_stmt with image B's cut lists. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPropBInt7.v at 6aea585e8b5b for
   reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role (lib/AU/Img0.rsegs, lib/A/RPgBase
   and RPgCSpec, lib/AU/RPgSteps.v / RPgStepsU.v / RPgMem.v / RPgSeg.v / RPgPropKit.v / RPgPropLib.v names); every pc is
   role B's (SEL7 0x807b4, the memset call 0x80800 to 0x51608 with return 0x80804, the call of pod_write_ent 0x80818
   to 0x82bac with return 0x8081c, LATCH7 0x81d88); the real frame is 0x200 bytes and its cells are role B's (e.body
   in R+0xa0, &e in R+0xb8, pp in R+0x140); across the calls the block keeps the property index (t1) in s4, what is
   left of the input (t3) in s10 and the cursor (t4) in s8, and at its end it puts the cursor into a7, t3 and t1 back,
   s10 := -8 and `seen` (s2) into a2, so the clobbered set and the block's relation are role B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/AU/RPgPropIntB.v, with its module names changed; 174 of its 233 lines of code are new or changed and 694 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5CloseP.v at ada533759b23 for reac-pw/fuzz_rate's
   image A: module paths changed; rate's pcs (CL 0x82484 -> LATCH 0x82528), cut lists (lib/A/RtPgSeg.v: the cursor in
   R+0x100, the six header cells rs_Hc, the frame's 56 shadow bytes) and segment start (rs_start_M01 with its own
   rt_fsh and rt_cut conjuncts); rm_ / rl_ become rtm_ / rt_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5CloseP.v at a66696a9b1d1 for the same
   unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; image B's pcs (CL 0x824c0 -> LATCH 0x82578)
   and cut lists (lib/AU/RtPgSegB.v: at CL s2 = &pp->len, what is left in s9 and the cursor in s10; at LATCH the
   property index in t0, what is left in t4, s9 = 1 and `seen` in R+0x98; the frame's 88 shadow bytes); the piece
   writes no real-frame cell; the model lemmas use RtPgSegB's rsb_ vocabulary and the bridge lib/AU/RtPgW5SegB.v;
   the prefixes w5_ / rs_ / rtm_ become w5b_ / rsb_ / rtmb_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW5ClosePB.v at 2ebedbb4253d for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; role B's pcs
   (CL 0x81ccc -> LATCH 0x81d84) and cut lists (lib/AU/RPgSeg.v: at CL s6 = &pp->len, s4 = 1, what is left in s2 and
   the cursor in s8; at LATCH the property index in t1, what is left in t3, the cursor in a7 and `seen` in R+0x80);
   the real frame is 0x200 bytes; the cut vocabulary is RPgSeg's rs_, the bridge lib/AU/RPgW5Seg.v's w5_, the memory
   layer lib/AU/RPgMem.v's rm_; the prefixes w5b_ / rsb_ / rtmb_ become w5_ / rs_ / rm_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses from the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): the piece lemma of the params Struct's close
   in LLVMFuzzerTestOneInput (0x80020), CL 0x81ccc -> LATCH 0x81d84, as lib/AU/RPgSeg.v states it
   (rs_piece_W5_close_stmt). Proves no function (kind: segment lemma).

   HOW. The cut CL gives the code's facts (registers, real-frame cells, pp->len from the first block's image); the
   core walk (lib/AU/RPgW5Close.v w5_close_core) runs from them to 0x81d84; the cut LATCH is rebuilt from its post:
   the journal and frame part (RPgW5Seg w5_core_post), the (location, value) facts (kept, and t1 := the property
   index, t3 := what is left, a7 := the cursor from the core's post), the frame's shadow (kept), the first block's
   image (Model.pc_buf_close and the two flag words when the Struct is the first params property: RPgW5Seg
   w5_img_close_eq, w5_img_gen) and the model facts (Model.props_loop's Struct arm, from the cut's tie of the
   count and the pods to the input). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgMem RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW5Kit RPgW5Seg RPgW5Close.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

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
Local Arguments rs_cur {segs} _ _ _.

(* ---- the cell R+0xf8: ~pp, read as an unsigned word ---- *)
Lemma w5_lnot_mod : forall p, 0 <= p < 2 ^ 64 -> Z.lnot p mod 2 ^ 64 = 18446744073709551615 - p.
Proof.
intros p Hp. unfold Z.lnot, Z.pred. symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

(* ---- the model at the close ---- *)
Lemma w5_wf_close : forall sh ps es, rs_wf sh ps -> (length ps <= 2)%nat -> Forall ent_wf es ->
(length es <= 32)%nat -> rs_wf sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]).
Proof.
intros sh ps es (Hs & Hk & He & Hl) H2 Hes Hn.
assert (HK : 0 <= POD_PROP_PARAMS < 2 ^ 32) by (unfold POD_PROP_PARAMS; split; [lia | apply Z.ltb_lt; reflexivity]).
split; [exact Hs|]. split.
- apply Forall_app. split; [exact Hk|]. constructor; [split; [exact HK | exact Hn] | constructor].
- split; [unfold all_ents in *; rewrite flat_map_app; cbn [flat_map snd]; rewrite app_nil_r;
          apply Forall_app; split; assumption|].
  rewrite length_app. cbn [length]. lia.
Qed.
Lemma w5_seen_close : forall ps es, rs_seen (ps ++ [(POD_PROP_PARAMS, PStruct es)]) = 1.
Proof.
intros ps es. unfold rs_seen. rewrite existsb_app. cbn [existsb fst]. rewrite Z.eqb_refl. cbn [orb].
rewrite orb_true_r. reflexivity.
Qed.
Lemma w5_loop_close : forall sh ps cnt es rest r, sh <> 7 ->
ps = fst (props_loop sh (length ps) (rs_r0 rest)) -> rs_pod_tie sh ps cnt es rest r -> Z.of_nat (length es) = cnt ->
(ps ++ [(POD_PROP_PARAMS, PStruct es)], r) =
props_loop sh (length (ps ++ [(POD_PROP_PARAMS, PStruct es)])) (rs_r0 rest).
Proof.
intros sh ps cnt es rest r Hsh Hps (sel & c & r1 & r2 & Hs1 & Hc & Hcnt & Hm4 & Hb4 & He) Hlen.
rewrite length_app. cbn [length]. rewrite Nat.add_1_r. rewrite props_loop_S_end.
remember (props_loop sh (length ps) (rs_r0 rest)) as pl eqn:EL. destruct pl as [ps0 r0].
cbn [fst snd] in Hps, Hs1. subst ps0. cbv beta iota.
unfold prop_step. rewrite <- Hs1. cbv beta iota.
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
replace (sel mod 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hm4).
rewrite Hb4. cbv beta iota. rewrite <- Hc. cbv beta iota.
rewrite <- Hcnt, <- Hlen, Nat2Z.id, He. reflexivity.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma w5_piece_close : rs_piece_W5_close_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W5_close_stmt. intros cx POST rest i Hst HL.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (w5_pre_facts B LAWS cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
unfold rs_from_CL. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r Hlen Hcut.
destruct Hcut as (Hcore & Hat & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen1 & Hps & Htie & Hsh & Hnp & Hpsnp & Hnp3 & Hsh7 &
  Hps2 & Hcnt & Hesw & Hescnt).
unfold rs_at_cx in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walk takes ---- *)
assert (A2 : getr regs2 2 = w64 (e_R (x_e cx))).
{ rewrite <- (w5_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w5_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
pose proof (w5_at_reg _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(w5_in)) as A9.
pose proof (w5_at_reg _ _ _ _ _ 22 (e_pp (x_e cx) + 0x4000) Hat ltac:(w5_in)) as A22.
pose proof (w5_at_reg _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(w5_in)) as A27.
pose proof (w5_at_reg _ _ _ _ _ 20 1 Hat ltac:(w5_in)) as A20.
pose proof (w5_at_reg _ _ _ _ _ 18 (Z.of_nat (length r)) Hat ltac:(w5_in)) as A18.
pose proof (w5_at_reg _ _ _ _ _ 24 (rs_cur cx rest r) Hat ltac:(w5_in)) as A24.
pose proof (w5_at_cell _ _ _ _ _ 0x148 (shadow_addr (e_pp (x_e cx) + 0x4000)) Hat ltac:(w5_in)) as V148.
pose proof (w5_at_cell _ _ _ _ _ 0x98 (Z.of_nat (length ps)) Hat ltac:(w5_in)) as V98.
pose proof (w5_at_cell _ _ _ _ _ 0x88 (e_pp (x_e cx) + rs_at_of sh ps) Hat ltac:(w5_in)) as V88.
pose proof (w5_at_cell _ _ _ _ _ 0x90 (rs_at_of sh ps) Hat ltac:(w5_in)) as V90.
pose proof (w5_at_cell _ _ _ _ _ 0xf8 (Z.lnot (e_pp (x_e cx))) Hat ltac:(w5_in)) as Vf8.
pose proof (w5_at_cell _ _ _ _ _ 0x78 (e_pp (x_e cx) + 0x400c) Hat ltac:(w5_in)) as V78.
pose proof (w5_at_cell _ _ _ _ _ 0x138 (rs_first ps) Hat ltac:(w5_in)) as V138.
pose proof (w5_at_cell _ _ _ _ _ 0x50 (e_pp (x_e cx) + 0x4010) Hat ltac:(w5_in)) as V50.
pose proof (w5_plen_lo sh ps Hsh7) as Hplen.
pose proof (w5_buf_open_len sh ps es) as Hbuf.
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_open sh ps es Hv He Hesw) as [Hblen _].
set (len := Z.of_nat (length (pc_buf (PbCut sh ps (Some es))))) in *.
assert (Hat16 : 16 <= rs_at_of sh ps) by (unfold rs_at_of; lia).
assert (Hal : rs_at_of sh ps + 8 <= len) by (unfold rs_at_of; lia).
assert (H5440 : len <= 5440) by lia.
pose proof (w5_first_range ps) as Hfr.
assert (Hnr : 0 <= Z.of_nat (length r) < 2 ^ 64).
{ destruct Hin as (Hl & _ & _ & _ & _ & Hs0 & Hs63 & _). destruct Hsuf as (j & Hj & ->).
  rewrite length_skipn. lia. }
assert (Hcur : 0 <= rs_cur cx rest r < 2 ^ 64).
{ destruct Hin as (Hl & _ & _ & _ & _ & Hs0 & Hs63 & _). destruct Hsuf as (j & Hj & ->).
  unfold rs_cur. rewrite length_skipn. lia. }
assert (Hnps : 0 <= Z.of_nat (length ps) < 2 ^ 64) by lia.
assert (HSA : 0 <= shadow_addr (e_pp (x_e cx) + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_pos (e_pp (x_e cx) + 0x4000) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (e_pp (x_e cx) + 0x4000) 8 (e_pp (x_e cx) + 0x4000) ltac:(lia) ltac:(lia)).
  lia. }
rewrite Z.mod_small in V148 by lia. rewrite Z.mod_small in V98 by lia.
rewrite Z.mod_small in V88 by (unfold PP_SIZE in *; lia). rewrite Z.mod_small in V90 by lia.
rewrite (w5_lnot_mod (e_pp (x_e cx))) in Vf8 by (unfold PP_SIZE in *; lia).
rewrite Z.mod_small in V78 by (unfold PP_SIZE in *; lia). rewrite Z.mod_small in V138 by lia.
rewrite Z.mod_small in V50 by (unfold PP_SIZE in *; lia).
assert (Hes32 : (length es <= 32)%nat) by lia.
pose proof (w5_ents_bounds sh ps (Some es) Hwf (conj Hesw Hes32)) as (EB1 & EB2).
assert (Old : rm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))) by exact Hpp.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 len).
{ refine (rm_pp_len rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
(* ---- the core walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs RS_CL regs2 mem2 md2) with (cfg_at rsegs 0x81ccc regs2 mem2 md2).
  exact (w5_close_core B MT MTL LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (rs_at_of sh ps) len
    (rs_first ps) (Z.of_nat (length ps)) (Z.of_nat (length r)) (rs_cur cx rest r) HJ Ppin2 Ppout A2 A9 A22 A27 A20
    A18 A24 V148 V98 V88 V90 Vf8 V78 V138 V50 Vlen RB3 RB1 RB2 Hat16 Hal H5440 Hfr Hnps Hnr Hcur). }
intros W3 c3 Hle Hpost.
assert (HEp : forall a, (e_pp (x_e cx) + rs_at_of sh ps <= a < e_pp (x_e cx) + rs_at_of sh ps + 4) \/
  (rs_first ps = 1 /\ e_pp (x_e cx) + 0x400c <= a < e_pp (x_e cx) + 0x4014) -> rs_E1 rsegs cx a).
{ intros a [Ha|[_ Ha]]; apply w5_E1_pp; unfold PP_SIZE; lia. }
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) ->
  ~ In (Z_to_bv 5 r0) [6; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv).
{ intros r0 [-> | [-> | ->]]; w5_notin. }
destruct (w5_core_post B MT MTL cx (rs_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x81d84
  [6; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv _ W3 c3 Hcore HEp Hclob Hpost)
  as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rsz & Rfl & R6 & R28 & R17)).
assert (Hsp : spZ regs2 = e_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* every byte the piece did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
  ~ (e_pp (x_e cx) + rs_at_of sh ps <= a < e_pp (x_e cx) + rs_at_of sh ps + 4) ->
  ~ (rs_first ps = 1 /\ e_pp (x_e cx) + 0x400c <= a < e_pp (x_e cx) + 0x4014) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3. apply Hmem; [exact Ha | rewrite Hsp; exact H1 |]. intros [X|X]; auto. }
(* the real frame [R, R + 0x200): the piece writes none of its cells *)
assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x200 ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
(* ---- the cut LATCH ---- *)
change (cfg_at rsegs 0x81d84 regs3 mem3 md3) with (cfg_at rsegs RS_LATCH regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 sh np (ps ++ [(POD_PROP_PARAMS, PStruct es)]) r);
  [rewrite length_app, Hlen; cbn [length]; lia|].
split.
- split; [exact Hcore3|].
  split.
  { unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros j Hj.
    change (length rs_P0) with 88%nat in Hj.
    pose proof (Z.mul_div_le (e_F (x_e cx)) 8 ltac:(lia)) as D1.
    pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)) as D2.
    unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in PApp.
    apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
  split.
  { unfold rs_pp_at.
    change (rm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))).
    rewrite (w5_img_close_eq sh ps es Hsh7). fold len.
    assert (LB1 : length (overwrite (pc_buf (PbCut sh ps (Some es))) (Z.to_nat (rs_at_of sh ps))
        (le32 (len - rs_at_of sh ps - 8))) = length (pc_buf (PbCut sh ps (Some es)))).
    { apply length_overwrite. rewrite length_le32. lia. }
    assert (Nb : rm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (overwrite (pc_buf (PbCut sh ps (Some es)))
        (Z.to_nat (rs_at_of sh ps)) (le32 (len - rs_at_of sh ps - 8)))).
    { apply (rm_bytes_patch rsegs (w_H W2) mem2); [exact (w5_img_buf _ _ _ _ _ _ _ _ _ Old) | | |].
      - rewrite Z2Nat.id by lia. exact Rsz.
      - rewrite length_le32. lia.
      - intros y Hy1 Hy2. rewrite length_le32 in Hy2. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia;
        intros [_ X]; lia. }
    apply (w5_img_gen (w_H W2) mem2 (w_H W3) mem3 (e_pp (x_e cx)) (pc_buf (PbCut sh ps (Some es))) _ _
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
    - rewrite LB1. lia.
    - rewrite LB1. unfold POD_BUF_MAX. lia.
    - exact EB1.
    - exact EB2.
    - rewrite LB1. unfold OFF_LEN. eapply val_mem_kept; [|exact Vlen]. intros k0 Hk0. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *;
        try lia; intros [_ X]; lia.
    - destruct (Z.eqb_spec (rs_first ps) 1) as [E|E].
      + rewrite orb_true_r. exact (proj1 (Rfl E)).
      + rewrite orb_false_r. refine (proj1 (w5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
        intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia;
        intros [X _]; exact (E X).
    - destruct (Z.eqb_spec (rs_first ps) 1) as [E|E].
      + rewrite orb_true_r. exact (proj2 (Rfl E)).
      + rewrite orb_false_r. refine (proj2 (w5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
        intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia;
        intros [X _]; exact (E X).
    - intros y Hy. rewrite LB1 in Hy. unfold OFF_LEN, OFF_IS_PROPS, OFF_HAS_PARAMS, OFF_ENT, PP_SIZE in Hy.
      apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
  split; [exact Hin|]. split; [exact Hsuf|].
  split; [apply w5_wf_close; [exact Hwf | exact Hps2 | exact Hesw | lia]|].
  split; [exact Hsh|]. split; [exact Hnp|].
  split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hnp3|].
  exact (w5_loop_close sh ps cnt es rest r Hsh7 Hps Htie Hescnt).
- unfold rs_at_cx, rs_at, rs_L_LATCH.
  rewrite (w5_seen_close ps es).
  replace (Z.of_nat (length (ps ++ [(POD_PROP_PARAMS, PStruct es)])) - 1) with (Z.of_nat (length ps))
    by (rewrite length_app; cbn [length]; lia).
  cbn [rs_Rc rs_Rc0 rs_Kc app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: first [ w5_kept Hat Hkeep Kc | exact R6 | exact R28 | exact R17 ].
Qed.
End p.
